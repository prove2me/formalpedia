-- Prove2me | solution 1 for ReviewInfoShare.eq_5_second_stage_prices
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:27:35.386297+00:00
-- url     : https://prove2.me/submissions/868049c2-8a83-4dcd-98eb-5aa017f9fbf6

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Wholesale

namespace Aux_RIS5

lemma pmax_exists0 (D w : ℝ) :
    IsMaxOn (fun p => (p - w) * (D - p)) Set.univ ((D + w) / 2) := by
  rw [isMaxOn_iff]; intro p _
  nlinarith [sq_nonneg (p - (D + w) / 2)]

lemma pmax_unique0 (D w x : ℝ) (h : IsMaxOn (fun p => (p - w) * (D - p)) Set.univ x) :
    x = (D + w) / 2 := by
  have := isMaxOn_iff.mp h ((D + w) / 2) (Set.mem_univ _)
  nlinarith [sq_nonneg (x - (D + w) / 2)]

lemma wmax_exists0 (D c : ℝ) :
    IsMaxOn (fun w => (w - c) * (D - (D + w) / 2)) Set.univ ((D + c) / 2) := by
  rw [isMaxOn_iff]; intro p _
  nlinarith [sq_nonneg (p - (D + c) / 2)]

end Aux_RIS5

open ReviewInfoShare in
theorem solution (P : Params) (q : Quality) :
    (∃ p₂ w₂, IsWholesaleStage2Eq P q p₂ w₂) ∧
    ∀ p₂ w₂, IsWholesaleStage2Eq P q p₂ w₂ → ∀ t z : ℝ,
      (p₂ (w₂ t z) t z = (3 * P.α + 3 * t * z + P.cost q) / 4 ∧
        w₂ t z = (P.α + t * z + P.cost q) / 2) ∧
      (p₂ (w₂ P.μ z) t z = (3 * P.α + (2 * t + P.μ) * z + P.cost q) / 4 ∧
        w₂ P.μ z = (P.α + P.μ * z + P.cost q) / 2) := by
  refine ⟨⟨fun w t z => (P.α + t * z + w) / 2, fun t z => (P.α + t * z + P.cost q) / 2,
    fun w t z => Aux_RIS5.pmax_exists0 _ _, fun t z => Aux_RIS5.wmax_exists0 _ _⟩, ?_⟩
  intro p₂ w₂ h
  have hp : ∀ w t z, p₂ w t z = (P.α + t * z + w) / 2 := fun w t z =>
    Aux_RIS5.pmax_unique0 _ _ _ (h.1 w t z)
  have hw : ∀ t z, w₂ t z = (P.α + t * z + P.cost q) / 2 := by
    intro t z
    have h2 := isMaxOn_iff.mp (h.2 t z) ((P.α + t * z + P.cost q) / 2) (Set.mem_univ _)
    rw [hp, hp] at h2
    nlinarith [sq_nonneg (w₂ t z - (P.α + t * z + P.cost q) / 2)]
  intro t z
  refine ⟨⟨?_, hw t z⟩, ⟨?_, hw P.μ z⟩⟩
  · rw [hp, hw]; ring
  · rw [hp, hw]; ring
