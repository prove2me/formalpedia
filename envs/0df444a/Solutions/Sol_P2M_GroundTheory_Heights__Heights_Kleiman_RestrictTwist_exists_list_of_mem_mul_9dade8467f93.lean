-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_list_of_mem_mul_9dade8467f93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:28.190938+00:00
-- url     : https://prove2.me/submissions/7fb560a8-d8ba-449c-abc8-261de0293c8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {A : Type*} [CommRing A] [Algebra A Ω] {P Q : Submodule A Ω} {z : Ω}
    (hz : z ∈ P * Q) :
    ∃ l : List (Ω × Ω), (∀ p ∈ l, p.1 ∈ P ∧ p.2 ∈ Q) ∧ (l.map fun p => p.1 * p.2).sum = z := by
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem m hm n hn => exact ⟨[(m, n)], by simp [hm, hn], by simp⟩
  | add a _ b _ ha hb =>
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨l', hl', rfl⟩ := hb
    exact ⟨l ++ l', fun p hp => (List.mem_append.mp hp).elim (hl p) (hl' p), by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
