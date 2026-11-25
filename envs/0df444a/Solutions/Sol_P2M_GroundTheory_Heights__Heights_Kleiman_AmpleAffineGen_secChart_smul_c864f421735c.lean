-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_smul_c864f421735c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:55.880071+00:00
-- url     : https://prove2.me/submissions/c4f61db9-8461-4087-abc2-ddd080e939b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_twist_pow_d77a3231d657


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
theorem _root_.solution {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I : Chart x} {a z : Ω}
    (ha : a ∈ ampleChart H m h I) (hz : z ∈ secChart Q H m b h I) : a * z ∈ secChart Q H m b h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨k, hk⟩ := hz
  refine ⟨k + n, ?_⟩
  have h1 := AmpleTwistLocal.mul_mem_twist_pow Q H I hk hn
  have e1 : z * h ^ k * (a * h ^ n) = a * z * h ^ (k + n) := by ring
  have e2 : b + m * k + m * n = b + m * (k + n) := by rw [Nat.mul_add, Nat.add_assoc]
  rwa [e1, e2] at h1
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
