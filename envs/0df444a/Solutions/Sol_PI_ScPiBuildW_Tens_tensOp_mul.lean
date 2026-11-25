-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.tensOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:10.139119+00:00
-- url     : https://prove2.me/submissions/c57943af-ecc5-4720-bd3e-54bf7aadf159

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
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
theorem _root_.solution (A B : ∀ i, Vl i →L[ℂ] Vl i) :
    tensOp (fun i => A i * B i) = tensOp A * tensOp B :=
  clm_ext fun x => by
    rw [ContinuousLinearMap.mul_apply, tensOp_tensU, tensOp_tensU, tensOp_tensU]
    rfl
end PI.ScPiBuildW.Tens
