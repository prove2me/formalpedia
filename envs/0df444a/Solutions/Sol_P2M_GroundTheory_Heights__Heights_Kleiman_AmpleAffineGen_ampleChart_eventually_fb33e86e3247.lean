-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_eventually_fb33e86e3247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:21.24453+00:00
-- url     : https://prove2.me/submissions/e961d5b1-3f41-4b15-b288-16d3647278fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619


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
theorem _root_.solution {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I : Chart x}
    (hh : h ∈ (H.pow m).sub I) {a : Ω} (ha : a ∈ ampleChart H m h I) :
    ∀ᶠ e in Filter.atTop, a * h ^ e ∈ (H.pow (m * e)).sub I := by
  obtain ⟨n, hn⟩ := ha
  refine Filter.eventually_atTop.mpr ⟨n, fun e he => ?_⟩
  have h1 := AmpleTwistLocal.mul_mem_pow H I hn _ (AmpleTwistLocal.pow_mem_pow H I hh (e - n))
  have e1 : a * h ^ n * h ^ (e - n) = a * h ^ e := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' he]
  have e2 : m * n + m * (e - n) = m * e := by rw [← Nat.mul_add, Nat.add_sub_cancel' he]
  rwa [e1, e2] at h1
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
