-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.lie_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:43:58.229888+00:00
-- url     : https://prove2.me/submissions/e2b8ccf9-c412-4e24-9240-2ab9a960e6fc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint

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
theorem _root_.solution {i : Fin (r + 1)} {X : Mx k r} (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hS : SuppV i X) :
    inLieLev k r i X := by
  refine ⟨hU, fun a ha => ⟨?_, ?_⟩⟩
  · funext p
    simp only [bvec, Matrix.mulVec_single_one, Pi.zero_apply]
    refine hS _ _ (Or.inr ?_)
    have := a.isLt
    unfold Out eI
    simp only
    omega
  · funext p
    simp only [bvec, Matrix.mulVec_single_one, Pi.zero_apply]
    refine hS _ _ (Or.inr ?_)
    have := a.isLt
    unfold Out esI
    simp only
    omega
end PI.QnHermHaar.HermitianAdjointLemmas
