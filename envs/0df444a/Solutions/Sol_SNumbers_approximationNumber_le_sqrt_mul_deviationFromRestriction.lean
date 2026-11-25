-- Prove2me | solution 1 for SNumbers.approximationNumber_le_sqrt_mul_deviationFromRestriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:40.113342+00:00
-- url     : https://prove2.me/submissions/652e1803-3882-4dd2-8530-7709ea0ae90b

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
public import Theorems.Thm_SNumbers_norm_comp_le_deviationFromRestriction_mul
public import Theorems.Thm_ContinuousLinearMap_rank_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg
public import Theorems.Thm_SNumbers_exists_projection_ker_eq_of_codim_le


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution
    (S : X →L[𝕜] Y) {n : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X))
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromRestriction S M := by
  have hdev0 : 0 ≤ deviationFromRestriction S M := deviationFromRestriction_nonneg S M
  -- The Garling–Gordon projection is available only up to `ε`; take `ε → 0`.
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / (deviationFromRestriction S M + 1) with hεdef
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨P, hP_idem, hP_ker, hP_norm⟩ :=
    exists_projection_ker_eq_of_codim_le hM_closed hM_codim hε
  -- `rank P = codim (ker P) = codim M ≤ n`.
  have hPrank : P.rank ≤ (n : Cardinal) := by
    have e : Module.rank 𝕜 (X ⧸ LinearMap.ker (P : X →ₗ[𝕜] X))
              = Module.rank 𝕜 (LinearMap.range (P : X →ₗ[𝕜] X)) :=
      (LinearMap.quotKerEquivRange (P : X →ₗ[𝕜] X)).rank_eq
    rw [hP_ker] at e
    calc P.rank = Module.rank 𝕜 (LinearMap.range (P : X →ₗ[𝕜] X)) := rfl
      _ = Module.rank 𝕜 (X ⧸ M) := e.symm
      _ ≤ (n : Cardinal) := hM_codim
  -- `L := S ∘ P` is an admissible rank-≤ n approximant.
  have hL_rank : (S.comp P).rank ≤ (n : Cardinal) := by
    have h := ContinuousLinearMap.rank_comp_comp_le (ContinuousLinearMap.id 𝕜 X) P S
    rw [ContinuousLinearMap.comp_id] at h
    exact h.trans hPrank
  -- `id − P` lands in `M` (its range is `ker P = M`).
  have hR : ∀ x, (ContinuousLinearMap.id 𝕜 X - P) x ∈ M := by
    intro x
    have hPP : P (P x) = P x := by
      have h : (P.comp P) x = P x := by rw [hP_idem]
      exact h
    have hkey : P ((ContinuousLinearMap.id 𝕜 X - P) x) = 0 := by
      rw [sub_apply, ContinuousLinearMap.id_apply, map_sub,
        hPP, sub_self]
    rw [← hP_ker, LinearMap.mem_ker]
    exact hkey
  -- `‖id − P‖ ≤ 1 + (√n + ε)`.
  have h4 : ‖(ContinuousLinearMap.id 𝕜 X - P : X →L[𝕜] X)‖ ≤ 1 + (Real.sqrt n + ε) :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hP_norm)
  -- `dev · ε ≤ δ`, so the `ε` term is absorbed into `δ`.
  have hdevε : deviationFromRestriction S M * ε ≤ δ := by
    rw [hεdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [hdev0, hδ.le]
  calc approximationNumber S n
      ≤ ‖S - S.comp P‖ := approximationNumber_le_norm_sub hL_rank
    _ = ‖S.comp (ContinuousLinearMap.id 𝕜 X - P)‖ := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    _ ≤ deviationFromRestriction S M *
          ‖(ContinuousLinearMap.id 𝕜 X - P : X →L[𝕜] X)‖ :=
        norm_comp_le_deviationFromRestriction_mul hR
    _ ≤ deviationFromRestriction S M * (1 + (Real.sqrt n + ε)) :=
        mul_le_mul_of_nonneg_left h4 hdev0
    _ = (1 + Real.sqrt n) * deviationFromRestriction S M
          + deviationFromRestriction S M * ε := by ring
    _ ≤ (1 + Real.sqrt n) * deviationFromRestriction S M + δ := by gcongr
end SNumbers
