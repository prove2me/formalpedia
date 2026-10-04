-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v4
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:07:43.992923+00:00
-- url     : https://prove2.me/submissions/7cda0796-bde0-4e43-8be9-58c475f07b06

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Fin

theorem solution (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by
  have hcheck : ∀ d : Fin 111, Odd d.val → (2 * d.val - 1).Prime →
      (∀ r : Fin 111, r.val.Prime → r.val ∣ d.val → r.val = 3 ∨ r.val = 5 ∨ r.val = 23) →
      d.val = 3 ∨ d.val = 9 ∨ d.val = 15 ∨ d.val = 27 ∨ d.val = 45 ∨ d.val = 69 ∨ d.val = 75 := by
    decide +kernel
  have hDpos : 0 < D := by
    have hp2 := hp.two_le
    omega
  apply hcheck ⟨D, hDlt⟩ hDodd (by simpa only [hp_eq] using hp)
  intro r hr hd
  rcases hDsupport r.val hr hd with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have := Nat.le_of_dvd hDpos hd
    omega

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
