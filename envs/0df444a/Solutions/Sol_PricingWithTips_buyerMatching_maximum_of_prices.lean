-- Prove2me | solution 1 for PricingWithTips.buyerMatching_maximum_of_prices
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:26:20.589764+00:00
-- url     : https://prove2.me/submissions/0e47193c-1c71-43df-a429-b58ce013a83c

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

private theorem buyerMatching_sum_prices (z : BuyerMatching B S) (p : S → ℝ) :
    (∑ b, match z.assigned b with | none => 0 | some s => p s) =
      ∑ s, if ∃ b, z.assigned b = some s then p s else 0 := by
  classical
  have hpoint (b : B) :
      (match z.assigned b with | none => 0 | some s => p s) =
        ∑ s, if z.assigned b = some s then p s else 0 := by
    cases h : z.assigned b with
    | none => simp [h]
    | some s => simp [h]
  calc
    (∑ b, match z.assigned b with | none => 0 | some s => p s) =
        ∑ b, ∑ s, if z.assigned b = some s then p s else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          exact hpoint b
    _ = ∑ s, ∑ b, if z.assigned b = some s then p s else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s, if ∃ b, z.assigned b = some s then p s else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : ∃ b, z.assigned b = some s
          · obtain ⟨b₀, hb₀⟩ := h
            have hequiv (b : B) : (z.assigned b = some s) ↔ b = b₀ := by
              constructor
              · intro hb
                exact z.store_unique hb hb₀
              · intro hb
                subst b
                exact hb₀
            have hh : ∃ b, z.assigned b = some s := ⟨b₀, hb₀⟩
            simp only [if_pos hh]
            simp_rw [hequiv]
            simp
          · have hnone (b : B) : z.assigned b ≠ some s := by
              intro hb
              exact h ⟨b, hb⟩
            simp [h, hnone]

theorem solution
    (z : BuyerMatching B S) (q : B → S → ℝ) (p : S → ℝ)
    (hp : ∀ s, 0 ≤ p s)
    (hbuyer : ∀ b,
      match z.assigned b with
      | none => ∀ s, q b s - p s ≤ 0
      | some s =>
          0 ≤ q b s - p s ∧ ∀ s', q b s' - p s' ≤ q b s - p s)
    (hunsold : ∀ s, (¬ ∃ b, z.assigned b = some s) → p s = 0) :
    IsMaximumWeight z q := by
  classical
  let u : B → ℝ := fun b =>
    match z.assigned b with
    | none => 0
    | some s => q b s - p s
  have hu : ∀ b, 0 ≤ u b := by
    intro b
    cases h : z.assigned b with
    | none => simp [u, h]
    | some s =>
        have hb := hbuyer b
        simp only [h] at hb
        simpa [u, h] using hb.1
  have hdual : ∀ b s, q b s ≤ u b + p s := by
    intro b s
    cases h : z.assigned b with
    | none =>
        have hb := hbuyer b
        simp only [h] at hb
        simp only [u, h]
        linarith [hb s]
    | some s₀ =>
        have hb := hbuyer b
        simp only [h] at hb
        have hb' := hb.2 s
        simp only [u, h]
        linarith
  have hprice (z' : BuyerMatching B S) :
      (∑ b, match z'.assigned b with | none => 0 | some s => p s) ≤ ∑ s, p s := by
    rw [buyerMatching_sum_prices]
    apply Finset.sum_le_sum
    intro s _
    split_ifs with hs
    · exact le_refl _
    · exact hp s
  have hupper (z' : BuyerMatching B S) :
      matchingWeight z' q ≤ (∑ b, u b) + (∑ s, p s) := by
    calc
      matchingWeight z' q ≤
          ∑ b, (u b + match z'.assigned b with | none => 0 | some s => p s) := by
            unfold matchingWeight
            apply Finset.sum_le_sum
            intro b _
            cases h : z'.assigned b with
            | none => simp [h, hu b]
            | some s => simpa [h] using hdual b s
      _ = (∑ b, u b) +
          (∑ b, match z'.assigned b with | none => 0 | some s => p s) := by
            rw [Finset.sum_add_distrib]
      _ ≤ (∑ b, u b) + (∑ s, p s) := by
            gcongr
            exact hprice z'
  have hprice_eq :
      (∑ b, match z.assigned b with | none => 0 | some s => p s) = ∑ s, p s := by
    rw [buyerMatching_sum_prices]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs with hs
    · rfl
    · simp [hunsold s hs]
  have hweight_eq : matchingWeight z q = (∑ b, u b) + (∑ s, p s) := by
    calc
      matchingWeight z q =
          ∑ b, (u b + match z.assigned b with | none => 0 | some s => p s) := by
            unfold matchingWeight
            apply Finset.sum_congr rfl
            intro b _
            cases h : z.assigned b with
            | none => simp [u, h]
            | some s => simp [u, h]
      _ = (∑ b, u b) +
          (∑ b, match z.assigned b with | none => 0 | some s => p s) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ b, u b) + (∑ s, p s) := by rw [hprice_eq]
  intro z'
  rw [hweight_eq]
  exact hupper z'
