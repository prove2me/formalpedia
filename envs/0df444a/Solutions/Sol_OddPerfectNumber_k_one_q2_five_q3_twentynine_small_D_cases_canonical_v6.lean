-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v6
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:36:20.350424+00:00
-- url     : https://prove2.me/submissions/53f19eb0-a1fe-42c0-8742-b4a2f5ee78d5

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Fin

theorem solution (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) :
    D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  have hcheck : ∀ d : Fin 75, 15 < d.val → Odd d.val → (2 * d.val - 1).Prime →
      (∀ r : Fin 30, r.val.Prime → r.val ∣ d.val → r.val = 3 ∨ r.val = 5 ∨ r.val = 29) →
      d.val = 27 ∨ d.val = 31 ∨ d.val = 37 ∨ d.val = 45 := by
    decide +kernel
  apply hcheck ⟨D, hDlt⟩ hDgt hDodd (by simpa only [hp_eq] using hp)
  intro r hr hd
  rcases hDsupport r.val hr hd with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have := r.isLt
    omega

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
