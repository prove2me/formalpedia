-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:21:45.980209+00:00
-- url     : https://prove2.me/submissions/546b53da-ead0-4143-abe2-c7cff574a150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmpleAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
theorem _root_.solution (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (H.pow m).sub I) (n : ℕ) : h ^ n ∈ (H.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_mem_twistMod_zero I
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow H I ih m hh
end GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
