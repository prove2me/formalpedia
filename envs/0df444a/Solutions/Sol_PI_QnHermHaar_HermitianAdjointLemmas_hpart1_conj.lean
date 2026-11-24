-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.hpart1_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:43:55.675904+00:00
-- url     : https://prove2.me/submissions/6ea90f38-352f-405b-b01c-70c4254ec304

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_inv
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_ct
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_hpk
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq


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
theorem _root_.solution (Z : Mx k r) :
    hpart1 (Hpk k r) (Hpk k r * Zᴴ * Hpk k r) = -hpart1 (Hpk k r) Z := by
  unfold hpart1
  rw [hpk_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hpk_ct]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  rw [← smul_neg, neg_sub]
end PI.QnHermHaar.HermitianAdjointLemmas
