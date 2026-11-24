-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.supp_hmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:43:49.063377+00:00
-- url     : https://prove2.me/submissions/e87877fb-219a-471a-b7cc-0b48084f20fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_out_tau
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_mul_apply


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
theorem _root_.solution {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (Hpk k r * A) := by
  intro p q h
  rw [WeylGroupFacts.hpk_mul_apply]
  rcases h with hp | hq
  · rw [hA _ _ (Or.inl (out_tau hp)), mul_zero]
  · rw [hA _ _ (Or.inr hq), mul_zero]
end PI.QnHermHaar.HermitianAdjointLemmas
