-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.supp_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:42.940827+00:00
-- url     : https://prove2.me/submissions/3e81e4e9-6389-463d-9510-5d0f62993cf4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_ct
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_hmul
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_mulh

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
theorem _root_.solution {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (Hpk k r * Aᴴ * Hpk k r) :=
  supp_mulh (supp_hmul (supp_ct hA))
end PI.QnHermHaar.HermitianAdjointLemmas
