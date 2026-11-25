-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensSpan_sum_mul_mem_localized_eeeb4b33e5e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:41:02.549841+00:00
-- url     : https://prove2.me/submissions/f02599dc-d4c5-4623-8d51-a5191243de7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensSpan
theorem _root_.solution {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    exact ⟨n, by rw [← mul_assoc]; exact mul_mem hn (ht q)⟩
end TwistedDualGensSpan
end GroundTheory.Heights₂.Heights.NumbersDVR
