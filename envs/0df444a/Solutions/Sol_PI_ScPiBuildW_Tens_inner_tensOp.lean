-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.inner_tensOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:04.505634+00:00
-- url     : https://prove2.me/submissions/8fd657ab-5409-4747-9946-464c5d0f1d05

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_inner_tensU
import Theorems.Thm_PI_ScPiBuildW_Tens_eq_of_inner_tensU
import Theorems.Thm_PI_ScPiBuildW_Tens_clm_ext
import Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_tensU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Module
open PI PI.ScPiBuildW PI.ScPiBuildW.Tens
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]
namespace PI.ScPiBuildW.Tens
theorem _root_.solution (A : ∀ i, Vl i →L[ℂ] Vl i) (hA : ∀ i (u w : Vl i), ⟪A i u, A i w⟫_ℂ = ⟪u, w⟫_ℂ)
    (u w : TV Vl) : ⟪tensOp A u, tensOp A w⟫_ℂ = ⟪u, w⟫_ℂ := by
  have hQ : (ContinuousLinearMap.adjoint (tensOp A)) * tensOp A = 1 := clm_ext fun y => by
    refine eq_of_inner_tensU fun x => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right, tensOp_tensU,
      tensOp_tensU, ContinuousLinearMap.one_apply, inner_tensU, inner_tensU]
    exact Finset.prod_congr rfl fun i _ => hA i (x i) (y i)
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply, hQ,
    ContinuousLinearMap.one_apply]
end PI.ScPiBuildW.Tens
