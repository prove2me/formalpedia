-- Prove2me | solution 1 for SNumbers.deviationFromSubspace_comp_comp_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:20:31.823181+00:00
-- url     : https://prove2.me/submissions/a891196f-c728-4c7e-b5fd-d049cbe20601

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_Submodule_liftQL_mkQL
public import Theorems.Thm_Submodule_norm_liftQL_le
public import Theorems.Thm_Submodule_norm_mkQL_le
attribute [local simp] Submodule.liftQL_mkQL



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
theorem _root_.solution
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (B.comp (S.comp A)) (V.map (B : Y →ₗ[𝕜] Z))
      ≤ ‖B‖ * ‖A‖ * deviationFromSubspace S V := by
  unfold deviationFromSubspace
  -- The CLM `(V.map B).mkQL ∘ B : Y →L[𝕜] Z/(V.map B)` has `V` in its
  -- kernel: for `v ∈ V`, `B v ∈ V.map B`, hence `[B v]_{Z/(V.map B)} = 0`.
  -- It therefore descends through `V.mkQL` via `V.liftQL` to a CLM
  -- `Y/V →L[𝕜] Z/(V.map B)` whose norm is bounded by `‖B‖`.
  set BL : Y →L[𝕜] (Z ⧸ V.map (B : Y →ₗ[𝕜] Z)) :=
    (V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B with hBL_def
  have h_ker :
      V ≤ LinearMap.ker (BL : Y →ₗ[𝕜] (Z ⧸ V.map (B : Y →ₗ[𝕜] Z))) := by
    intro v hv
    show (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B v) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨v, hv, rfl⟩
  have h_BL_norm : ‖BL‖ ≤ ‖B‖ := by
    rw [hBL_def]
    calc ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B‖
        ≤ ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL‖ * ‖B‖ := opNorm_comp_le _ _
      _ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right
          (V.map (B : Y →ₗ[𝕜] Z)).norm_mkQL_le (norm_nonneg _)
      _ = ‖B‖ := one_mul _
  have h_lift_norm : ‖V.liftQL BL h_ker‖ ≤ ‖B‖ :=
    (V.norm_liftQL_le BL h_ker).trans h_BL_norm
  -- Pointwise bound on `w : W`.
  have h_bound_nn : 0 ≤ ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg A))
      (norm_nonneg (V.mkQL.comp S))
  refine opNorm_le_bound _ h_bound_nn fun w => ?_
  show ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL (B (S (A w)))‖ ≤
       ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ * ‖w‖
  -- Apply the descent: `BL (S (A w)) = V.liftQL BL _ (V.mkQL (S (A w)))`.
  have h_apply : (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B (S (A w)))
      = V.liftQL BL h_ker (V.mkQL (S (A w))) :=
    (V.liftQL_mkQL BL h_ker (S (A w))).symm
  rw [h_apply]
  calc ‖V.liftQL BL h_ker (V.mkQL (S (A w)))‖
      ≤ ‖V.liftQL BL h_ker‖ * ‖(V.mkQL.comp S) (A w)‖ :=
        (V.liftQL BL h_ker).le_opNorm _
    _ ≤ ‖B‖ * ‖(V.mkQL.comp S) (A w)‖ :=
        mul_le_mul_of_nonneg_right h_lift_norm (norm_nonneg _)
    _ ≤ ‖B‖ * (‖V.mkQL.comp S‖ * ‖A w‖) :=
        mul_le_mul_of_nonneg_left ((V.mkQL.comp S).le_opNorm (A w))
          (norm_nonneg B)
    _ ≤ ‖B‖ * (‖V.mkQL.comp S‖ * (‖A‖ * ‖w‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (A.le_opNorm w)
            (norm_nonneg (V.mkQL.comp S)))
          (norm_nonneg B)
    _ = ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ * ‖w‖ := by ring
end SNumbers
