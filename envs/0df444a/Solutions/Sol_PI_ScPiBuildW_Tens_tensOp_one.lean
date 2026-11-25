-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.tensOp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:16.949514+00:00
-- url     : https://prove2.me/submissions/0a1f5308-119b-4b69-b517-451293660386

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
theorem _root_.solution : tensOp (fun i => (1 : Vl i →L[ℂ] Vl i)) = 1 :=
  clm_ext fun x => by rw [tensOp_tensU]; rfl
end PI.ScPiBuildW.Tens
