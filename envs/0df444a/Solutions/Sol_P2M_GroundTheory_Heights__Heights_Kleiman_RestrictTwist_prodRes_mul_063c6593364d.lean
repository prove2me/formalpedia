-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_mul_063c6593364d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:57.511015+00:00
-- url     : https://prove2.me/submissions/83fa5faf-20b7-4cf8-b48b-4049f582387b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem__7be37290911c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_list_sum_of_d239f93787f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_mul_of_ede9904075bf

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
theorem _root_.solution {Q₁ Q₂ : SubSystem S x Ω} {Q₁' Q₂' : SubSystem S y K'} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁ hxy Q₁' r₁) (h₂ : RestrictData Q₂ hxy Q₂' r₂) (I : Chart y)
    {l : List (Ω × Ω)} (hl : ∀ p ∈ l, p.1 ∈ Q₁.sub (liftChart hxy I) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy I), p.2 * a ∈ chartRing S x (liftChart hxy I))
    (hl1 : (l.map fun p => p.1 * p.2).sum = 1) {a b : Ω} (ha : a ∈ Q₁.sub (liftChart hxy I))
    (hb : b ∈ Q₂.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l (b * a) = r₁ a * r₂ b := by
  have ha' : a = (l.map fun p => (p.2 * a) * p.1).sum := by
    calc a = a * (l.map fun p => p.1 * p.2).sum := by rw [hl1, mul_one]
      _ = (l.map fun p => a * (p.1 * p.2)).sum := (List.sum_map_mul_left ..).symm
      _ = _ := congrArg List.sum (List.map_congr_left fun p _ => by ring)
  have key : r₁ a = (l.map fun p => red S x y I.1 (p.2 * a) * r₁ p.1).sum := by
    conv_lhs => rw [ha']
    rw [map_list_sum_of h₁ I _ ?_, List.map_map]
    · exact congrArg List.sum (List.map_congr_left fun p hp =>
        map_mul_of h₁ I ((hl p hp).2 a ha) (hl p hp).1)
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact mul_mem' ((hl p hp).2 a ha) (hl p hp).1
  rw [key, prodRes, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [show p.2 * (b * a) = (p.2 * a) * b by ring, map_mul_of h₂ I ((hl p hp).2 a ha) hb]
  ring
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
