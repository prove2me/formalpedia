-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_smul_ec967148cc37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:31.314845+00:00
-- url     : https://prove2.me/submissions/56f01621-84cc-4944-8b13-d625cebc500c

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
namespace CombAfterPower
theorem _root_.solution {d : D} (h : CombAfterPower c z s (c • d)) :
    CombAfterPower c z s d := by
  obtain ⟨k, f, hf⟩ := h
  exact ⟨k + 1, f, by rw [pow_succ, mul_smul, hf]⟩
end CombAfterPower
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
