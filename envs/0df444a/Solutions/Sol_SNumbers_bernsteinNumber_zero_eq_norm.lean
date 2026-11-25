-- Prove2me | solution 1 for SNumbers.bernsteinNumber_zero_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:49:06.307821+00:00
-- url     : https://prove2.me/submissions/0156b6eb-b70b-4000-8cb0-2caf55b8b3aa

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
public import Theorems.Thm_SNumbers_le_gainOnSubspace
public import Theorems.Thm_SNumbers_gainOnSubspace_le_norm
public import Theorems.Thm_SNumbers_bddAbove_bernsteinSet
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
private lemma gainOnSubspace_span_singleton {S : X →L[𝕜] Y} {v : X} (hv_ne : v ≠ 0) :
    gainOnSubspace S (Submodule.span 𝕜 {v}) = ‖S v‖ / ‖v‖ := by
  set M : Submodule 𝕜 X := Submodule.span 𝕜 {v}
  have hv_mem : v ∈ M := Submodule.subset_span (Set.mem_singleton _)
  have hM_ne_bot : M ≠ ⊥ := fun hM_bot =>
    hv_ne (by rwa [hM_bot, Submodule.mem_bot] at hv_mem)
  refine le_antisymm (gainOnSubspace_le_div hv_mem hv_ne) ?_
  refine le_gainOnSubspace hM_ne_bot ?_
  rintro _ hx_mem hx_ne
  rw [Submodule.mem_span_singleton] at hx_mem
  obtain ⟨c, rfl⟩ := hx_mem
  have hc_ne : c ≠ 0 := fun hc => hx_ne (by rw [hc, zero_smul])
  rw [map_smul, norm_smul, norm_smul,
      mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hc_ne)]
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) :
    bernsteinNumber S 0 = ‖S‖ := by
  refine le_antisymm
    (Real.sSup_le (fun _ ⟨M, _, hr⟩ => hr.symm ▸ gainOnSubspace_le_norm S M)
      (norm_nonneg _)) ?_
  -- For each `v` with `‖v‖ ≠ 0`, the 1-dim subspace `span {v}` realises
  -- the gain `‖S v‖/‖v‖`, which is therefore `≤ b_0 S`.
  refine opNorm_le_bound' _ (bernsteinNumber_nonneg S 0) fun v hv_norm => ?_
  have hv_ne : v ≠ 0 := norm_ne_zero_iff.mp hv_norm
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hM_rank : Module.rank 𝕜 (Submodule.span 𝕜 ({v} : Set X)) = ((0 + 1 : ℕ) : Cardinal) := by
    rw [rank_span_set (LinearIndepOn.singleton hv_ne), Cardinal.mk_singleton]; norm_cast
  have h_le : gainOnSubspace S (Submodule.span 𝕜 ({v} : Set X)) ≤ bernsteinNumber S 0 :=
    le_csSup (bddAbove_bernsteinSet S 0) ⟨_, hM_rank, rfl⟩
  rw [gainOnSubspace_span_singleton hv_ne, div_le_iff₀ hv_pos] at h_le
  linarith
end SNumbers
