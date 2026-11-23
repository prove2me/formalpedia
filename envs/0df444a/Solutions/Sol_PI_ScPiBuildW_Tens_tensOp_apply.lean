-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.tensOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:58.949054+00:00
-- url     : https://prove2.me/submissions/c4614ab9-02f3-46c1-b8a6-90882415ab6a

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
theorem _root_.solution (A : ∀ i, Vl i →L[ℂ] Vl i) (v : TV Vl) (p : Idx Vl) :
    tensOp A v p = ∑ q, opMat A p q * v q := by
  simp only [tensOp, LinearMap.coe_toContinuousLinearMap']
  rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
end PI.ScPiBuildW.Tens
