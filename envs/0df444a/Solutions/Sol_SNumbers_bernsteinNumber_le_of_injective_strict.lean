-- Prove2me | solution 1 for SNumbers.bernsteinNumber_le_of_injective_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:12:16.440731+00:00
-- url     : https://prove2.me/submissions/08014e6c-b5ce-4a0d-bf41-3f575a6a54b9

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_le_sn_of_boundedBelow_strict
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm

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
theorem _root_.solution {s : Family 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : Injective s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ s S n := by
  refine Real.sSup_le ?_ (hs.nonneg S n)
  rintro _ ⟨M, hM_rank, rfl⟩
  -- Goal: `gainOnSubspace S M ≤ s S n`.
  set c := gainOnSubspace S M with hc_def
  rcases lt_or_ge 0 c with hcpos | hc0
  · -- `dim M = n+1`, so `n < finrank M`.
    have hfin : n < Module.finrank 𝕜 (M : Submodule 𝕜 X) := by
      rw [Module.finrank_eq_of_rank_eq hM_rank]; exact Nat.lt_succ_self n
    -- `S|_M = S ∘ M.subtypeL` is bounded below by `c` on `M`.
    have hf : ∀ x : M, c * ‖x‖ ≤ ‖(S.comp M.subtypeL) x‖ := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · have hx' : (x : X) ≠ 0 := fun h => hx (Subtype.ext h)
        have hpos : 0 < ‖(x : X)‖ := norm_pos_iff.mpr hx'
        have hle : c ≤ ‖S (x : X)‖ / ‖(x : X)‖ :=
          gainOnSubspace_le_div x.2 hx'
        have hmul : c * ‖(x : X)‖ ≤ ‖S (x : X)‖ := (le_div_iff₀ hpos).mp hle
        simpa using hmul
    -- Core bound and the (S3) step back to `S`.
    have hcore : c ≤ s (S.comp M.subtypeL) n :=
      le_sn_of_boundedBelow_strict hs hinj hfin hcpos (S.comp M.subtypeL) hf
    have hback : s (S.comp M.subtypeL) n ≤ s S n := by
      have h_ideal := hs.ideal M.subtypeL S (ContinuousLinearMap.id 𝕜 Y) n
      rw [ContinuousLinearMap.id_comp] at h_ideal
      have hsn : 0 ≤ s S n := hs.nonneg S n
      have hidY : ‖ContinuousLinearMap.id 𝕜 Y‖ ≤ 1 := norm_id_le
      have hsub : ‖M.subtypeL‖ ≤ 1 := M.norm_subtypeL_le
      have t1 : ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n ≤ 1 * s S n :=
        mul_le_mul_of_nonneg_right hidY hsn
      have t2 := mul_le_mul t1 hsub (norm_nonneg M.subtypeL)
        (by rw [one_mul]; exact hsn)
      calc s (S.comp M.subtypeL) n
          ≤ ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n * ‖M.subtypeL‖ := h_ideal
        _ ≤ 1 * s S n * 1 := t2
        _ = s S n := by ring
    exact hcore.trans hback
  · exact hc0.trans (hs.nonneg S n)
end SNumbers
