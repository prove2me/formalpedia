-- Prove2me | solution 1 for PositivityTheory.ThKF.E.sympl_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:36.02263+00:00
-- url     : https://prove2.me/submissions/ef10ad94-0b6b-49c9-b706-7ad7e5a43c40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_EqOfInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKF.E
theorem _root_.solution (w u : l ⊕ l → ℝ) : sympl w u = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ u) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Matrix.one_apply, Fintype.sum_sum_type,
    mul_comm, sub_eq_add_neg, add_comm]
end PositivityTheory.ThKF.E
