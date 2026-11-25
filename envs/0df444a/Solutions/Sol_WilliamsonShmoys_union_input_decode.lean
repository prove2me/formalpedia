-- Prove2me | solution 1 for WilliamsonShmoys.union_input_decode
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T10:54:55.453679+00:00
-- url     : https://prove2.me/submissions/33a8eac3-f179-4366-a69b-bd266e0c1714

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false

open WilliamsonShmoys

namespace DEC

lemma pos_lt (n k c v w : ℕ) (hc : c < k) (hv : v < n) (hw : w < n) :
    (c * n + v) * (k * n) + (c * n + w) < (k * n) * (k * n) := by
  have h1 : c * n + v < k * n := by
    have := Nat.mul_le_mul_right n (show c + 1 ≤ k by omega)
    have e : (c + 1) * n = c * n + n := by ring
    omega
  have h2 : c * n + w < k * n := by
    have := Nat.mul_le_mul_right n (show c + 1 ≤ k by omega)
    have e : (c + 1) * n = c * n + n := by ring
    omega
  have h3 := Nat.mul_le_mul_right (k * n) (show c * n + v + 1 ≤ k * n by omega)
  have e : (c * n + v + 1) * (k * n) = (c * n + v) * (k * n) + k * n := by ring
  omega

lemma div_mod_of (N i j : ℕ) (hj : j < N) : (i * N + j) / N = i ∧ (i * N + j) % N = j := by
  have hN : 0 < N := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

lemma cn_div (n c v : ℕ) (hv : v < n) : (c * n + v) / n = c ∧ (c * n + v) % n = v := by
  have := div_mod_of n c v hv; exact this

end DEC

open Classical in
theorem solution (n k : ℕ) (hn : 0 < n) (mk : ℕ → ℕ) (eb : ℕ → ℕ → ℕ) (wt : ℕ → ℝ)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h1 : M 1 = k * n) (h3 : M 3 = 3 * k)
    (hT : ∀ c v w, c < k → v < n → w < n → M (5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) =
      if mk v ≠ c ∧ mk w ≠ c ∧ 1 ≤ eb v w then 1 else 0)
    (hO : ∀ a, a % 2 = 1 → a ≠ 1 → a ≠ 3 →
      (∀ c v w, c < k → v < n → w < n → a ≠ 5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) → M a = 0)
    (hR : ∀ c v, c < k → v < n → R (2 * (c * n + v) + 1) = if mk v ≠ c then wt v else 0)
    (hRO : ∀ a, a % 2 = 1 → (∀ c v, c < k → v < n → a ≠ 2 * (c * n + v) + 1) → R a = 0) :
    (∀ a, M (2 * a + 1) = (planarRAMInput (k * n)
      (3 * k) (fun x y => decide (x.val / n = y.val / n ∧ mk (x.val % n) ≠ x.val / n ∧ mk (y.val % n) ≠ x.val / n ∧
        1 ≤ eb (x.val % n) (y.val % n)))
      (fun x => if mk (x.val % n) ≠ x.val / n then wt (x.val % n) else 0)).natMem a) ∧
    (∀ a, R (2 * a + 1) = (planarRAMInput (k * n)
      (3 * k) (fun x y => decide (x.val / n = y.val / n ∧ mk (x.val % n) ≠ x.val / n ∧ mk (y.val % n) ≠ x.val / n ∧
        1 ≤ eb (x.val % n) (y.val % n)))
      (fun x => if mk (x.val % n) ≠ x.val / n then wt (x.val % n) else 0)).realMem a) := by
  set N := k * n with hN
  constructor
  · intro a
    simp only [planarRAMInput]
    by_cases a0 : a = 0
    · subst a0; simp [h1]
    by_cases a1 : a = 1
    · subst a1; simp [h3]
    rw [if_neg a0, if_neg a1]
    set b := a - 2 with hb
    have hab : 2 * a + 1 = 5 + 2 * b := by omega
    by_cases hi : b / N < N
    · have hNpos : 0 < N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · rw [h] at hi; omega
        · exact h
      have hj : b % N < N := Nat.mod_lt _ hNpos
      rw [dif_pos hi, dif_pos hj]
      have hbd : b = (b / N) * N + b % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod b N).symm
      set i := b / N with hi'
      set j := b % N with hj'
      have hik : i / n < k := by
        rw [Nat.div_lt_iff_lt_mul hn]; rw [hN] at hi; exact hi
      have hjk : j / n < k := by
        rw [Nat.div_lt_iff_lt_mul hn]; rw [hN] at hj; exact hj
      have hvi : i % n < n := Nat.mod_lt _ hn
      have hwj : j % n < n := Nat.mod_lt _ hn
      have ei : i = (i / n) * n + i % n := by rw [Nat.mul_comm]; exact (Nat.div_add_mod i n).symm
      have ej : j = (j / n) * n + j % n := by rw [Nat.mul_comm]; exact (Nat.div_add_mod j n).symm
      by_cases hc : i / n = j / n
      · have hpos : 2 * a + 1 = 5 + 2 * (((i / n) * n + i % n) * N + ((i / n) * n + j % n)) := by
          rw [hab, hbd, ← ei]; congr 2; rw [hc, ← ej]
        rw [hpos, hT (i / n) (i % n) (j % n) hik hvi hwj]
        by_cases hcond : mk (i % n) ≠ i / n ∧ mk (j % n) ≠ i / n ∧ 1 ≤ eb (i % n) (j % n)
        · rw [if_pos hcond, if_pos (decide_eq_true ⟨hc, hcond.1, hcond.2.1, hcond.2.2⟩)]
        · rw [if_neg hcond, if_neg (fun h => hcond (by
            have h' := of_decide_eq_true h
            exact ⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩))]
      · rw [hO _ (by omega) (by omega) (by omega) ?_]
        · rw [if_neg (by simp; intro h; exact absurd h hc)]
        · intro c v w hck hv hw heq
          have hb2 : b = (c * n + v) * N + (c * n + w) := by omega
          have hcw : c * n + w < N := by
            have := Nat.mul_le_mul_right n (show c + 1 ≤ k by omega)
            have e : (c + 1) * n = c * n + n := by ring
            omega
          obtain ⟨d1, d2⟩ := DEC.div_mod_of N (c * n + v) (c * n + w) hcw
          rw [← hb2] at d1 d2
          have := DEC.cn_div n c v hv
          have := DEC.cn_div n c w hw
          apply hc
          rw [hi', hj', d1, d2]
          omega
    · rw [dif_neg hi]
      apply hO _ (by omega) (by omega) (by omega)
      intro c v w hck hv hw heq
      have := DEC.pos_lt n k c v w hck hv hw
      apply hi
      have hb2 : b = (c * n + v) * N + (c * n + w) := by omega
      have hNp : 0 < N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · rw [hN] at h; rw [h] at this; omega
        · exact h
      exact (Nat.div_lt_iff_lt_mul hNp).2 (by rw [hb2]; exact this)
  · intro a
    simp only [planarRAMInput]
    by_cases ha : a < N
    · rw [dif_pos ha]
      have hak : a / n < k := by rw [Nat.div_lt_iff_lt_mul hn]; rw [hN] at ha; exact ha
      have ea : a = (a / n) * n + a % n := by rw [Nat.mul_comm]; exact (Nat.div_add_mod a n).symm
      have := hR (a / n) (a % n) hak (Nat.mod_lt _ hn)
      rw [← ea] at this
      rw [this]
    · rw [dif_neg ha]
      apply hRO _ (by omega)
      intro c v hc hv heq
      apply ha
      have h1' : c * n + v < N := by
        have := Nat.mul_le_mul_right n (show c + 1 ≤ k by omega)
        have e : (c + 1) * n = c * n + n := by ring
        omega
      omega
