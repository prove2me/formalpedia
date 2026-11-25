-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_mul_d12ec9174181
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:58.032181+00:00
-- url     : https://prove2.me/submissions/6c31f984-4115-42e2-8b47-58efca8f34ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_res_mul_mem_pow_2beb75b9e3f6

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {H : SubSystem S x Ω} {σ : Ω} {I : Chart x}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {a b : Ω} (ha : a ∈ ampleChart H 1 σ I) (hb : b ∈ ampleChart H 1 σ I) :
    a * b ∈ ampleChart H 1 σ I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  have := H.res_mul_mem_pow I hn m hm
  convert this using 1; ring
end GroundTheory.Heights₂.Heights.Kleiman
