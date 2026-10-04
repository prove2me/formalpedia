-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_support_cut
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T05:29:04.567278+00:00
-- url     : https://prove2.me/submissions/e67eec39-7e3b-4e42-8444-a54db0d73ea4

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Fin

set_option maxRecDepth 8192
set_option synthInstance.maxSize 256

theorem solution (D p q4 : Nat) (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61) (hq4dvd : q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    (D = 159 ∧ p = 317 ∧ q4 = 53) ∨ (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
    (D = 477 ∧ p = 953 ∧ q4 = 53) ∨ (D = 531 ∧ p = 1061 ∧ q4 = 59) ∨
    (D = 549 ∧ p = 1097 ∧ q4 = 61) := by
  have h7 : ¬ 7 ∣ D := by
    intro hd
    have h := hDsupport 7 (by decide) hd
    omega
  have h11 : ¬ 11 ∣ D := by
    intro hd
    have h := hDsupport 11 (by decide) hd
    omega
  have hqcheck : ∀ q : Fin 62, q.val.Prime → 47 < q.val →
      q.val = 53 ∨ q.val = 59 ∨ q.val = 61 := by decide +kernel
  have hqcases := hqcheck ⟨q4, by omega⟩ hq4 hq4gt
  change q4 = 53 ∨ q4 = 59 ∨ q4 = 61 at hqcases
  have hqge : 53 ≤ q4 := by rcases hqcases with h | h | h <;> omega
  obtain ⟨k, hk⟩ := hq4dvd
  have hmul := Nat.mul_le_mul_right k hqge
  have hkbound : k < 13 := by omega
  subst p
  subst D
  rcases hqcases with hq | hq | hq
  · subst q4
    have hcheck : ∀ k : Fin 13, 111 ≤ 53 * k.val → (2 * (53 * k.val) - 1).Prime →
        (2 * (53 * k.val) - 1) % 4 = 1 → k.val = 3 ∨ k.val = 9 := by decide +kernel
    have hkcases := hcheck ⟨k, hkbound⟩ hDlow hp hp4
    change k = 3 ∨ k = 9 at hkcases
    rcases hkcases with rfl | rfl <;> decide +kernel
  · subst q4
    have hcheck : ∀ k : Fin 13, 111 ≤ 59 * k.val → (2 * (59 * k.val) - 1).Prime →
        (2 * (59 * k.val) - 1) % 4 = 1 → ¬ 11 ∣ 59 * k.val →
        k.val = 3 ∨ k.val = 9 := by decide +kernel
    have hkcases := hcheck ⟨k, hkbound⟩ hDlow hp hp4 h11
    change k = 3 ∨ k = 9 at hkcases
    rcases hkcases with rfl | rfl <;> decide +kernel
  · subst q4
    have hcheck : ∀ k : Fin 13, 111 ≤ 61 * k.val → (2 * (61 * k.val) - 1).Prime →
        (2 * (61 * k.val) - 1) % 4 = 1 → ¬ 7 ∣ 61 * k.val →
        k.val = 9 := by decide +kernel
    have hkcase := hcheck ⟨k, hkbound⟩ hDlow hp hp4 h7
    change k = 9 at hkcase
    subst k
    decide +kernel

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
