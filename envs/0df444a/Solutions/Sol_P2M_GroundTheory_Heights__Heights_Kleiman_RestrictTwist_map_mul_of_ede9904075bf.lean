-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_mul_of_ede9904075bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:21.173278+00:00
-- url     : https://prove2.me/submissions/c9a875ae-503e-4790-865b-d8660b080f9e

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
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (I : Chart y) {a q : Ω}
    (ha : a ∈ chartRing S x (liftChart hxy I)) (hq : q ∈ Q.sub (liftChart hxy I)) :
    r (a * q) = red S x y I.1 a * r q := by
  classical
  have hex : ∃ t : Poly S N × Poly S N × ℕ, t.2.1 ∈ monos I.1 ∧ t.1.IsHomogeneous t.2.2 ∧
      t.2.1.IsHomogeneous t.2.2 ∧ a = aeval x t.1 / aeval x t.2.1 := by
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    exact ⟨(f, s, e), hs, hf, hse, rfl⟩
  obtain ⟨hs, hf, hse, ha'⟩ := Classical.choose_spec hex
  rw [red, dif_pos hex]
  have := h.smul I q hq _ _ _ hs hf hse
  rw [← ha'] at this
  exact this
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
