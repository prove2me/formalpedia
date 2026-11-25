-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_pow_mul_cancel_b1d87a2248dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:36.882258+00:00
-- url     : https://prove2.me/submissions/cace6cb5-22e0-43e1-9cd3-aa550acd1b47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
theorem _root_.solution {u p q y : Ω} (hpq : p * q = 1) (e D : ℕ) :
    (u ^ e * p) ^ D * (q ^ D * y) = u ^ (e * D) * y := by
  calc (u ^ e * p) ^ D * (q ^ D * y) = u ^ (e * D) * (p * q) ^ D * y := by ring
    _ = u ^ (e * D) * y := by rw [hpq, one_pow, mul_one]
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
