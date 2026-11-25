-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.tensOp_tensU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:45.527822+00:00
-- url     : https://prove2.me/submissions/913512be-8f86-4370-a7f5-8bda9a7e1a7f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_tensU_apply
import Theorems.Thm_PI_ScPiBuildW_Tens_prod_sum_pi
import Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_apply
import Theorems.Thm_PI_ScPiBuildW_Tens_sum_inner_op

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
theorem _root_.solution (A : ∀ i, Vl i →L[ℂ] Vl i) (x : ∀ i, Vl i) :
    tensOp A (tensU x) = tensU (fun i => A i (x i)) := by
  ext p
  rw [tensOp_apply, tensU_apply]
  simp only [opMat, tensU_apply, ← Finset.prod_mul_distrib]
  rw [← prod_sum_pi (fun i j => ⟪bas Vl i (p i), A i (bas Vl i j)⟫_ℂ * ⟪bas Vl i j, x i⟫_ℂ)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact sum_inner_op (A i) (bas Vl i) _ _
end PI.ScPiBuildW.Tens
