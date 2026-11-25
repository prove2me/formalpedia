-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.hpk_conj_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:12.890744+00:00
-- url     : https://prove2.me/submissions/64760d41-6313-4749-bc4b-dce44cb490c0

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
theorem _root_.solution (a' b' p q : Fin (2 * r + k + 1)) :
    (Hpk k r * (Matrix.single a' b' (1 : ℂ))ᴴ * Hpk k r) p q = Hpk k r p b' * Hpk k r a' q := by
  rw [Matrix.conjTranspose_single, star_one]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
end PI.QnHermHaar.HermitianAdjointLemmas
