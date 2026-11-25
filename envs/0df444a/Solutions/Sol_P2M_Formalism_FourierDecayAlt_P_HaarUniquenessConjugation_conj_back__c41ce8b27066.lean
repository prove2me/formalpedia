-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_conj_back__c41ce8b27066
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:08.816195+00:00
-- url     : https://prove2.me/submissions/8b46edb1-4ddf-47fc-a244-69a83f08b790

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation

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
theorem _root_.solution (hP : IsUnit P.det) (U : Mat k r) : P⁻¹ * (P * U * P⁻¹) * P = U := by
  have h : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  calc P⁻¹ * (P * U * P⁻¹) * P = (P⁻¹ * P) * U * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [h, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
