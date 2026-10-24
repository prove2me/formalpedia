-- Prove2me | solution 1 for PricingWithTips.maximumMatching_max_zero
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:04:14.423104+00:00
-- url     : https://prove2.me/submissions/b0842f6f-f52b-49db-a400-433427dacfe8

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

private theorem maximumMatching_matched_nonnegative
    (z : BuyerMatching B S) (q : B → S → ℝ)
    (hmax : IsMaximumWeight z q)
    {b : B} {s : S} (hmatch : z.assigned b = some s) :
    0 ≤ q b s := by
  classical
  let z' : BuyerMatching B S := {
    assigned := fun b' => if b' = b then none else z.assigned b'
    store_unique := by
      intro b₁ b₂ s' h₁ h₂
      by_cases hb₁ : b₁ = b
      · simp [hb₁] at h₁
      · by_cases hb₂ : b₂ = b
        · simp [hb₂] at h₂
        · exact z.store_unique (by simpa [hb₁] using h₁) (by simpa [hb₂] using h₂)
  }
  let f : B → ℝ := fun x => match z.assigned x with | none => 0 | some s' => q x s'
  let g : B → ℝ := fun x => match z'.assigned x with | none => 0 | some s' => q x s'
  have hpoint : ∀ x, f x = g x + if x = b then q b s else 0 := by
    intro x
    by_cases hx : x = b
    · subst x
      simp [f, g, z', hmatch]
    · simp only [f, g, z', if_neg hx]
      simp
  have hweight : matchingWeight z q = matchingWeight z' q + q b s := by
    change (∑ x, f x) = (∑ x, g x) + q b s
    calc
      (∑ x, f x) = ∑ x, (g x + if x = b then q b s else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hpoint x
      _ = (∑ x, g x) + q b s := by simp [Finset.sum_add_distrib]
  have hle := hmax z'
  rw [hweight] at hle
  linarith

theorem solution
    (z : BuyerMatching B S) (q : B → S → ℝ)
    (hmax : IsMaximumWeight z q) :
    IsMaximumWeight z (fun b s => max 0 (q b s)) := by
  classical
  have hz : matchingWeight z (fun b s => max 0 (q b s)) = matchingWeight z q := by
    unfold matchingWeight
    apply Finset.sum_congr rfl
    intro b _
    cases h : z.assigned b with
    | none => simp [h]
    | some s =>
        have hnonneg := maximumMatching_matched_nonnegative z q hmax h
        simp [h, max_eq_right hnonneg]
  intro z'
  let zPlus : BuyerMatching B S := {
    assigned := fun b =>
      match z'.assigned b with
      | none => none
      | some s => if 0 ≤ q b s then some s else none
    store_unique := by
      intro b₁ b₂ s h₁ h₂
      cases hfirst : z'.assigned b₁ with
      | none => simp [hfirst] at h₁
      | some s₁ =>
          cases hsecond : z'.assigned b₂ with
          | none => simp [hsecond] at h₂
          | some s₂ =>
              simp [hfirst] at h₁
              simp [hsecond] at h₂
              have hs₁ : s₁ = s := h₁.2
              have hs₂ : s₂ = s := h₂.2
              subst s₁
              subst s₂
              exact z'.store_unique hfirst hsecond
  }
  have hplus : matchingWeight z' (fun b s => max 0 (q b s)) =
      matchingWeight zPlus q := by
    unfold matchingWeight
    apply Finset.sum_congr rfl
    intro b _
    cases h : z'.assigned b with
    | none => simp [zPlus, h]
    | some s =>
        by_cases hn : 0 ≤ q b s
        · simp [zPlus, h, hn, max_eq_right hn]
        · have hn' : q b s ≤ 0 := le_of_lt (lt_of_not_ge hn)
          simp [zPlus, h, hn, max_eq_left hn']
  rw [hplus, hz]
  exact hmax zPlus
