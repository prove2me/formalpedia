-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_add_1bf00d984f76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:26.372465+00:00
-- url     : https://prove2.me/submissions/6be274bb-6f0d-484c-8d84-1f60457ef2ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_smul_sum_aeval_267bcc6b7a88

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
theorem _root_.solution {d e : D} (hd : CombAfterPower c z s d) (he : CombAfterPower c z s e) :
    CombAfterPower c z s (d + e) := by
  obtain ⟨k, f, hf⟩ := hd
  obtain ⟨l, g, hg⟩ := he
  refine ⟨k + l, fun t ↦ MvPolynomial.C (c ^ l) * f t + MvPolynomial.C (c ^ k) * g t, ?_⟩
  have h1 : c ^ (k + l) • d = c ^ l • (c ^ k • d) := by rw [smul_smul, ← pow_add, add_comm]
  have h2 : c ^ (k + l) • e = c ^ k • (c ^ l • e) := by rw [smul_smul, ← pow_add]
  rw [smul_add, h1, h2, hf, hg, smul_sum_aeval, smul_sum_aeval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_add, add_mul]
end CombAfterPower
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
