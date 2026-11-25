-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.rdV_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:58.338798+00:00
-- url     : https://prove2.me/submissions/7cd9f232-e3f1-41c6-8eda-a936eb2006a1

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
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : RdV (-X) f g = -RdV X f g := by
  unfold RdV
  have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • -X))) =
      fun t : ℝ => (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (-t) := by
    funext t
    simp only [Complex.ofReal_neg, smul_neg, neg_smul]
  rw [e]
  exact (deriv_comp_neg (f := fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (x := 0)).trans
    (by rw [neg_zero])
end PI.QnHermHaar.HermitianAdjointLemmas
