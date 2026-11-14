-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_event_exponential_reduction
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:02:12.219206+00:00
-- url     : https://prove2.me/submissions/a20245e8-3165-4884-8700-67181b6d31c0

import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_change_of_measure
import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_three_exponential_errors
import Mathlib
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (Ω : ℕ → Type) [∀ n, Fintype (Ω n)]
    (p q : ∀ n, Ω n → ℝ) (D H Good : ∀ n, Ω n → Prop) (admissible : ℕ → Prop)
    (A B C b c : ℝ) (N₀ : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : 0 < b) (hc : 0 < c)
    (hp : ∀ n x, 0 ≤ p n x) (hq : ∀ n x, 0 ≤ q n x)
    (hdens : ∀ n ≥ N₀, admissible n → ∀ x, H n x → Good n x → p n x ≤ Real.exp (b*n/2)*q n x)
    (hmiss : ∀ n ≥ N₀, admissible n → (∑ x, if D n x ∧ ¬ H n x then p n x else 0) ≤ A*Real.exp (-b*n))
    (hreference : ∀ n ≥ N₀, admissible n → (∑ x, if H n x then q n x else 0) ≤ B*Real.exp (-b*n))
    (htail : ∀ n ≥ N₀, admissible n → (∑ x, if ¬ Good n x then p n x else 0) ≤ C*Real.exp (-c*n)) :
    ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ, ∀ n ≥ N, admissible n →
      (∑ x, if D n x then p n x else 0) ≤ Real.exp (-r*n) := by
  classical
  obtain ⟨r,hr,N,hN⟩ := overlap_three_exponential_errors A B C b (b/2) c hA hB hC hb (by linarith) hc
  refine ⟨r,hr,max N N₀,?_⟩
  intro n hn hadm
  have hh := overlap_change_of_measure (p n) (q n) (D n) (H n) (Good n)
    (Real.exp (b*n/2)) (A*Real.exp (-b*n)) (B*Real.exp (-b*n)) (C*Real.exp (-c*n))
    (hp n) (hq n) (le_of_lt (Real.exp_pos _)) (hdens n (le_trans (le_max_right _ _) hn) hadm)
    (hmiss n (le_trans (le_max_right _ _) hn) hadm) (hreference n (le_trans (le_max_right _ _) hn) hadm)
    (htail n (le_trans (le_max_right _ _) hn) hadm)
  have heq : Real.exp (b*n/2) * (B*Real.exp (-b*n)) = B*Real.exp (-(b/2)*n) := by
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring
  rw [heq] at hh
  exact hh.trans (hN n (le_trans (le_max_left _ _) hn))
