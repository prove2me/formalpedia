-- Prove2me | solution 1 for PI.QnHermHaar.tst_bExt_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:10:50.780348+00:00
-- url     : https://prove2.me/submissions/c8beeae7-e0d6-4bb2-a84f-4917953494aa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.QnHermHaar
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) :
    ContDiff ℝ ∞ (bExt k r z i c) := by
  unfold bExt
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (ContDiff.sum fun l _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id l) (posL k r i c)))
end PI.QnHermHaar
