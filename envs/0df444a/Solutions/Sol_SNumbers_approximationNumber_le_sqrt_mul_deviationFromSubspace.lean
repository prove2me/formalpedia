-- Prove2me | solution 1 for SNumbers.approximationNumber_le_sqrt_mul_deviationFromSubspace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:42.244626+00:00
-- url     : https://prove2.me/submissions/c56b2c42-3a1b-41c0-b4db-a2ed990e5f81

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
public import Theorems.Thm_SNumbers_norm_comp_le_norm_mul_deviationFromSubspace
public import Theorems.Thm_ContinuousLinearMap_rank_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_deviationFromSubspace_nonneg
public import Theorems.Thm_SNumbers_exists_projection_range_eq_of_rank_le


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
    (S : X →L[𝕜] Y) {n : ℕ} {V : Submodule 𝕜 Y}
    (hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromSubspace S V := by
  obtain ⟨P, hP_idem, hP_range, hP_norm⟩ :=
    exists_projection_range_eq_of_rank_le hV_rank
  -- `rank P = dim (range P) = dim V ≤ n`.
  have hPrank : P.rank ≤ (n : Cardinal) := by
    calc P.rank = Module.rank 𝕜 (LinearMap.range (P : Y →ₗ[𝕜] Y)) := rfl
      _ = Module.rank 𝕜 V := by rw [hP_range]
      _ ≤ (n : Cardinal) := hV_rank
  -- `L := P ∘ S` is an admissible rank-≤ n approximant.
  have hL_rank : (P.comp S).rank ≤ (n : Cardinal) := by
    have h := ContinuousLinearMap.rank_comp_comp_le S P (ContinuousLinearMap.id 𝕜 Y)
    rw [ContinuousLinearMap.id_comp] at h
    exact h.trans hPrank
  -- `id − P` vanishes on `V` (since `P` fixes its range `V`).
  have hVker : V ≤ LinearMap.ker
      ((ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y) : Y →ₗ[𝕜] Y) := by
    intro v hv
    have hPv : P v = v := by
      rw [← hP_range] at hv
      obtain ⟨w, hw⟩ := hv
      have hPP : P (P w) = P w := by
        have h : (P.comp P) w = P w := by rw [hP_idem]
        exact h
      rw [← hw]; exact hPP
    rw [LinearMap.mem_ker]
    show (ContinuousLinearMap.id 𝕜 Y - P) v = 0
    rw [sub_apply, ContinuousLinearMap.id_apply, hPv, sub_self]
  -- `‖id − P‖ ≤ 1 + √n`.
  have h4 : ‖(ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y)‖ ≤ 1 + Real.sqrt n :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hP_norm)
  calc approximationNumber S n
      ≤ ‖S - P.comp S‖ := approximationNumber_le_norm_sub hL_rank
    _ = ‖(ContinuousLinearMap.id 𝕜 Y - P).comp S‖ := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
    _ ≤ ‖(ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y)‖ * deviationFromSubspace S V :=
        norm_comp_le_norm_mul_deviationFromSubspace hVker
    _ ≤ (1 + Real.sqrt n) * deviationFromSubspace S V :=
        mul_le_mul_of_nonneg_right h4 (deviationFromSubspace_nonneg S V)
end SNumbers
