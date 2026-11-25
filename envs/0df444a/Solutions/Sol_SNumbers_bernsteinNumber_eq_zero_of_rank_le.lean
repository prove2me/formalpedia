-- Prove2me | solution 1 for SNumbers.bernsteinNumber_eq_zero_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:55:31.830619+00:00
-- url     : https://prove2.me/submissions/2e813be5-8e90-44c8-b1e1-846a42171f0e

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
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
private lemma gainSet_bddBelow (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    BddBelow {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖} :=
  ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact div_nonneg (norm_nonneg _) (norm_nonneg _)⟩
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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    bernsteinNumber S n = 0 := by
  refine le_antisymm ?_ (bernsteinNumber_nonneg S n)
  refine Real.sSup_le ?_ le_rfl
  rintro _ ⟨M, hM_rank, rfl⟩
  -- We claim `gainOnSubspace S M ≤ 0`. Find `x ∈ M ∩ ker S` with `x ≠ 0`
  -- via rank-nullity on `f := S.domRestrict M : M →ₗ Y`.
  set f : M →ₗ[𝕜] Y := (S : X →ₗ[𝕜] Y).domRestrict M
  have h_rank_f_le : Module.rank 𝕜 (LinearMap.range f) ≤ (n : Cardinal) :=
    (Submodule.rank_mono <| by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩).trans hS
  have h_split :
      Module.rank 𝕜 (LinearMap.range f) + Module.rank 𝕜 (LinearMap.ker f)
        = Module.rank 𝕜 M := LinearMap.rank_range_add_rank_ker f
  -- `dim ker f ≥ 1` from the rank decomposition.
  have h_ker_pos : 0 < Module.rank 𝕜 (LinearMap.ker f) := by
    rw [hM_rank] at h_split
    by_contra h_le
    have h_zero : Module.rank 𝕜 (LinearMap.ker f) = 0 :=
      le_antisymm (not_lt.mp h_le) bot_le
    rw [h_zero, add_zero] at h_split
    have : (n + 1 : ℕ) ≤ (n : ℕ) := by
      exact_mod_cast h_split.symm.trans_le h_rank_f_le
    omega
  have h_ker_ne_bot : LinearMap.ker f ≠ ⊥ := fun h => by
    rw [h, rank_bot] at h_ker_pos; exact lt_irrefl _ h_ker_pos
  obtain ⟨⟨x, hx_mem⟩, hx_ker, hx_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot h_ker_ne_bot
  have hx_ne_zero : x ≠ 0 := fun h => hx_ne (by ext; exact h)
  have hSx : S x = 0 := hx_ker
  have h_zero_in :
      (0 : ℝ) ∈ {r : ℝ | ∃ y, y ∈ M ∧ y ≠ 0 ∧ r = ‖S y‖ / ‖y‖} :=
    ⟨x, hx_mem, hx_ne_zero, by rw [hSx, norm_zero, zero_div]⟩
  exact csInf_le (gainSet_bddBelow S M) h_zero_in
end SNumbers
