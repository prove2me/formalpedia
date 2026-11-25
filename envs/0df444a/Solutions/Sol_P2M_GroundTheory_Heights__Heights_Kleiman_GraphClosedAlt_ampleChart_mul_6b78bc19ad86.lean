-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_mul_6b78bc19ad86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:28.482181+00:00
-- url     : https://prove2.me/submissions/c14d17e5-23c8-4ced-8981-5b23daa1520e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9


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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a b : Ω}
    (ha : a ∈ ampleChart H 1 h I) (hb : b ∈ ampleChart H 1 h I) : a * b ∈ ampleChart H 1 h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  rw [SubSystem.pow_sub] at hn hm ⊢
  rw [pow_add, pow_add]
  have : a * b * (h ^ n * h ^ m) = (a * h ^ n) * (b * h ^ m) := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn hm
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
