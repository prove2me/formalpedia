-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.hpk_out_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:45.31655+00:00
-- url     : https://prove2.me/submissions/4311c1ae-461f-48ce-85f0-d4ba8e53acfa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_out_tau
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau


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
theorem _root_.solution {i : Fin (r + 1)} {q m : Fin (2 * r + k + 1)} (hq : Out i q) (hm : ¬ Out i m) :
    Hpk k r m q = 0 := by
  rw [WeylGroupFacts.hpk_row, if_neg]
  intro h
  apply hm
  have := out_tau (k := k) hq
  rw [h, WeylGroupFacts.tau_tau] at this
  exact this
end PI.QnHermHaar.HermitianAdjointLemmas
