-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.supp_hpart2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:40.532274+00:00
-- url     : https://prove2.me/submissions/40458dda-7eaa-4ad8-aab1-ce5640923257

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_inv
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_add
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_smul
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_conj

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
theorem _root_.solution {i : Fin (r + 1)} {W : Mx k r} (hW : SuppV i W) : SuppV i (hpart2 (Hpk k r) W) := by
  unfold hpart2
  rw [hpk_inv]
  exact supp_smul (supp_add hW (supp_conj hW)) _
end PI.QnHermHaar.HermitianAdjointLemmas
