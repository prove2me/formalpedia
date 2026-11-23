-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.tensU_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:06.578802+00:00
-- url     : https://prove2.me/submissions/035167d3-e9a5-4201-8301-f654e5253e56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp

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
theorem _root_.solution (x : ∀ i, Vl i) (p : Idx Vl) : tensU x p = ∏ i, ⟪bas Vl i (p i), x i⟫_ℂ := rfl
end PI.ScPiBuildW.Tens
