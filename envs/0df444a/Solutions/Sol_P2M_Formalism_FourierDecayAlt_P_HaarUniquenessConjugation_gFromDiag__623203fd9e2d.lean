-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gFromDiag__623203fd9e2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:06:57.696277+00:00
-- url     : https://prove2.me/submissions/9974099e-bb37-4e9c-b7d6-e6666d579f9f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_haar_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_vol_crude

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
theorem _root_.solution (hE : UJEmb) (hU : Unimodular) (hV : VolGrowth) (hF : HpkFacts) (hC : UHConj) :
    HaarGExists ∧ VolCrude := by
  constructor
  · intro k r
    obtain ⟨-, -, -, ε, -, P, hP, hH⟩ := hF k r
    exact ⟨_, haar_map hE hU hC hP hH⟩
  · intro k r μG hμ
    obtain ⟨-, -, -, ε, -, P, hP, hH⟩ := hF k r
    exact vol_crude hE hV hC hP hH μG hμ
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
