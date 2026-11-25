-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_mem_bea31bfbe550
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:29.369488+00:00
-- url     : https://prove2.me/submissions/da3c5639-b0cb-46ff-bc5f-2fc519d62ac3

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
theorem _root_.solution {t : D} (ht : t ∈ s) : CombAfterPower c z s t := by
  classical
  refine ⟨0, fun u ↦ if u = t then 1 else 0, ?_⟩
  rw [pow_zero, one_smul, Finset.sum_eq_single t (fun b _ hb ↦ by simp [hb]) (fun h ↦ absurd ht h)]
  simp
end CombAfterPower
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
