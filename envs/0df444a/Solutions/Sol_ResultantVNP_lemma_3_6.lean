-- Prove2me | solution 1 for ResultantVNP.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T08:40:16.5672+00:00
-- url     : https://prove2.me/submissions/599ace4c-fe1d-4ce4-8c60-35f4a1ab6c98

import Mathlib

set_option autoImplicit false

namespace HyperdetGrid

/- The six-triangle cancellation used in the manuscript. -/
private lemma triple_spacing {m : ℕ}
    (b : ZMod m × ZMod m → ZMod 3) (h : ZMod m)
    (hb : ∀ i j, b (i, j) + b (i - h, j) + b (i, j - h) = 0) :
    ∀ i j, b (i, j) + b (i - 3 * h, j) + b (i, j - 3 * h) = 0 := by
  intro i j
  have h0 := hb i j
  have h1 := hb (i - h) j
  have h2 := hb i (j - h)
  have h3 := hb (i - 2 * h) j
  have h4 := hb (i - h) (j - h)
  have h5 := hb i (j - 2 * h)
  have hh : h + h = 2 * h := by ring
  have h2h : 2 * h + h = 3 * h := by ring
  simp only [sub_sub, hh, h2h] at h1 h2 h3 h4 h5
  have hc : (3 : ZMod 3) = 0 := by decide
  linear_combination (norm := ring_nf) h0 - h1 - h2 + h3 - h4 + h5
  simp only [hc, mul_zero]

private lemma power_spacing {m : ℕ}
    (b : ZMod m × ZMod m → ZMod 3)
    (hb : ∀ i j, b (i, j) + b (i - 1, j) + b (i, j - 1) = 0) (k : ℕ) :
    ∀ i j, b (i, j) + b (i - (3 ^ k : ℕ), j) + b (i, j - (3 ^ k : ℕ)) = 0 := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have h := triple_spacing b ((3 ^ k : ℕ) : ZMod m) ih
    simpa [pow_succ, Nat.cast_mul, mul_comm] using h

theorem constant_grid (r : ℕ) (hr : 1 ≤ r)
    (b : ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1) → ZMod 3)
    (hb : ∀ i j, b (i, j) + b (i - 1, j) + b (i, j - 1) = 0) :
    ∀ p q, b p = b q := by
  have hc : (3 : ZMod 3) = 0 := by decide
  have hq : ((3 ^ r : ℕ) : ZMod (3 ^ r + 1)) = -1 := by
    have h := ZMod.natCast_self (3 ^ r + 1)
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  have hrev : ∀ i j, b (i, j) + b (i + 1, j) + b (i, j + 1) = 0 := by
    simpa [hq] using power_spacing b hb r
  have hrow (i j : ZMod (3 ^ r + 1)) :
      b (i - 1, j) + b (i, j) + b (i + 1, j) = 0 := by
    have h1 := hrev i j
    have h2 := hrev (i - 1) j
    have h3 := hb i (j + 1)
    simp only [sub_add_cancel, add_sub_cancel_right] at h2 h3
    linear_combination h1 + h2 - h3
  have hperiod (i j : ZMod (3 ^ r + 1)) : b (i + 3, j) = b (i, j) := by
    have h1 := hrow (i + 1) j
    have h2 := hrow (i + 2) j
    have e : i + 2 - 1 = i + 1 := by ring
    simp only [add_sub_cancel_right, e, show i + 1 + 1 = i + 2 by ring,
      show i + 2 + 1 = i + 3 by ring] at h1 h2
    linear_combination h2 - h1
  have hperiod_mul (k : ℕ) (i j : ZMod (3 ^ r + 1)) :
      b (i + 3 * (k : ZMod (3 ^ r + 1)), j) = b (i, j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      rw [show i + 3 * ((k : ZMod (3 ^ r + 1)) + 1) = (i + 3 * k) + 3 by ring]
      rw [hperiod, ih]
  have hx (i j : ZMod (3 ^ r + 1)) : b (i + 1, j) = b (i, j) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have he : 3 * ((3 ^ k : ℕ) : ZMod (3 ^ r + 1)) = -1 := by
      calc
        _ = ((3 * 3 ^ k : ℕ) : ZMod (3 ^ r + 1)) := by push_cast; rfl
        _ = ((3 ^ r : ℕ) : ZMod (3 ^ r + 1)) := by rw [hk, pow_succ']
        _ = -1 := hq
    have h := hperiod_mul (3 ^ k) (i + 1) j
    rw [he, add_neg_cancel_right] at h
    exact h.symm
  have hy (i j : ZMod (3 ^ r + 1)) : b (i, j + 1) = b (i, j) := by
    have h1 := hrev i j
    rw [hx] at h1
    linear_combination (norm := ring_nf) h1
    simp [hc]
  have hxi (k : ℕ) (j : ZMod (3 ^ r + 1)) :
      b ((k : ZMod (3 ^ r + 1)), j) = b (0, j) := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [Nat.cast_add, Nat.cast_one, hx] using ih
  have hyi (k : ℕ) : b (0, (k : ZMod (3 ^ r + 1))) = b (0, 0) := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [Nat.cast_add, Nat.cast_one, hy] using ih
  have hconst (p : ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1)) : b p = b (0, 0) := by
    have h1 := hxi p.1.val p.2
    have h2 := hyi p.2.val
    simp only [ZMod.natCast_zmod_val] at h1 h2
    exact h1.trans h2
  intro p q
  exact (hconst p).trans (hconst q).symm

end HyperdetGrid

/-- Submission entry point: exactly the binders and conclusion of
    Prove2Me target 3f853f9f-f85b-4550-b08c-3a5a710b0c46. -/
theorem solution (r : ℕ) (hr : 1 ≤ r)
    (b : ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1) → ZMod 3)
    (hb : ∀ i j, b (i, j) + b (i - 1, j) + b (i, j - 1) = 0) :
    ∀ p q, b p = b q :=
  HyperdetGrid.constant_grid r hr b hb

#print axioms solution
