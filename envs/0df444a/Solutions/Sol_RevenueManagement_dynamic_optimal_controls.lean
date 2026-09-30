-- Prove2me | solution 1 for RevenueManagement.dynamic_optimal_controls
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-25T23:54:41.062386+00:00
-- url     : https://prove2.me/submissions/4672eb95-e97e-40fc-9882-e95da5794f64

import Mathlib
import Definitions.Def_RevenueManagement_singleResource

open RevenueManagement

theorem solution : ¬ (∀ (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C : ℕ)
    (hlam : IsArrivalModel lam n) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T),
    (∀ j, dynProtLevel lam p n T C t j ≤ dynProtLevel lam p n T C t (j + 1)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynProtLevel lam p n T C t (j - 1) < x then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if C - x < dynBookLimit lam p n T C t j then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynBidPrice lam p n T (t + 1) x ≤ p j then 1 else 0))) := by
  intro H
  let lam : ℕ → ℕ → ℝ := fun j _ => if j = 1 then 1 else 0
  let p : ℕ → ℝ := fun j => if j ≤ 1 then 1 else 0
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  have hlam : IsArrivalModel lam 2 := by
    refine ⟨fun j t => ?_, fun t => ?_⟩
    · simp only [lam]; split_ifs <;> norm_num
    · rw [hIcc]; simp [lam]
  have hp : ∀ j, 0 ≤ p j := fun j => by simp only [p]; split_ifs <;> norm_num
  have hanti : Antitone p := by
    intro a b hab
    simp only [p]
    split_ifs <;> first | omega | norm_num
  obtain ⟨_, _, _, h4⟩ := H lam p 2 2 1 hlam hp hanti 1 le_rfl (by norm_num)
  have hΔ : dynDelta lam p 2 2 2 1 = 1 := by
    simp [dynDelta, dynValue, dynValueGo, hIcc, lam, p]
  have hopt := h4 2 1 (by norm_num) le_rfl le_rfl le_rfl
  have hc : ¬ (dynBidPrice lam p 2 2 (1 + 1) 1 ≤ p 2) := by
    simp only [dynBidPrice, show (1 : ℕ) + 1 = 2 from rfl, hΔ, p]; norm_num
  rw [if_neg hc] at hopt
  have := hopt.2 (-1) (by norm_num)
  simp only [show (1 : ℕ) + 1 = 2 from rfl, hΔ, p] at this
  norm_num at this
