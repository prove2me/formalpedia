-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.supp_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:04:50.060803+00:00
-- url     : https://prove2.me/submissions/d5d55e28-361b-4007-9229-c7c53f4f9c97

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_not_out_posL

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
open PI.QnHermHaar.HermitianAdjointLemmas
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.QnHermHaar.HermitianAdjointLemmas
theorem _root_.solution (i : Fin (r + 1)) (c d : Fin (mdim k r i)) :
    SuppV i (Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) := by
  intro p q h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  rcases h with h | h <;> exact not_out_posL i _ h
end PI.QnHermHaar.HermitianAdjointLemmas
