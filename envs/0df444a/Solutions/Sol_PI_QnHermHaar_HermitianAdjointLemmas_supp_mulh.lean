-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.supp_mulh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:01.207898+00:00
-- url     : https://prove2.me/submissions/ae9d32df-ceed-4fa8-8036-ef816bbbff5e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_ct
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_ct
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_hmul

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
theorem _root_.solution {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (A * Hpk k r) := by
  have e : A * Hpk k r = (Hpk k r * Aᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct]
  rw [e]
  exact supp_ct (supp_hmul (supp_ct hA))
end PI.QnHermHaar.HermitianAdjointLemmas
