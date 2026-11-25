-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.ec_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:15:34.605821+00:00
-- url     : https://prove2.me/submissions/7f625bf0-b620-4d8a-b261-beefc5d3d0d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_hpart1
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_hpart2
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_inU_hpart1
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_inU_hpart2
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_lie_of

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
theorem _root_.solution {i : Fin (r + 1)} {L : Mx k r →L[ℝ] ℂ} {f : Mx k r → ℂ} {g : Mx k r}
    (hL : ∀ X, inLieLev k r i X → RdV X f g = L (g * X)) {W : Mx k r} (hW : SuppV i W) :
    RdV (hpart1 (Hpk k r) W) f g + Complex.I • RdV (hpart2 (Hpk k r) W) f g = phiL L g W := by
  rw [hL _ (lie_of (inU_hpart1 W) (supp_hpart1 hW)), hL _ (lie_of (inU_hpart2 W) (supp_hpart2 hW)),
    smul_eq_mul]
  rfl
end PI.QnHermHaar.HermitianAdjointLemmas
