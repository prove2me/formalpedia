-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_smul_sum_aeval_267bcc6b7a88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:37.952892+00:00
-- url     : https://prove2.me/submissions/8a4f43eb-7a61-405e-9bf2-e1404f5c1f3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}
variable {c : A} {z : Fin m → D} {s : Finset D}
namespace GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
theorem _root_.solution (b : A) (cf : D → MvPolynomial (Fin m) A) :
    b • ∑ t ∈ s, aeval z (cf t) * t = ∑ t ∈ s, aeval z (MvPolynomial.C b * cf t) * t := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_mul, MvPolynomial.aeval_C, Algebra.smul_def, mul_assoc]
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
