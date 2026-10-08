-- Prove2me | solution 1 for RegevLWE.Correctness.rounding
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:42:03.718466+00:00
-- url     : https://prove2.me/submissions/25378957-4769-40cf-91af-c5de60dde4dc

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem

open Matrix RegevLWE.Correctness

theorem solution {p : ℕ} [NeZero p] (hp : 2 ≤ p) (x : ZMod p)
    (hx : (absZ x : ℝ) < ((p / 2 : ℕ) : ℝ) / 2) :
    absZ x < absZ (x - ((p / 2 : ℕ) : ZMod p)) ∧
      decodeResidue x = 0 ∧
      decodeResidue (((p / 2 : ℕ) : ZMod p) + x) = 1 := by
  have hx' : 2 * absZ x < p / 2 := by
    have : (2 * absZ x : ℕ) < p / 2 := by
      exact_mod_cast (show (2 : ℝ) * (absZ x : ℝ) < ((p / 2 : ℕ) : ℝ) by linarith)
    exact this
  have hq : p / 2 < p := by omega
  have hval := x.val_lt
  have hc : (((p / 2 : ℕ) : ZMod p)).val = p / 2 := ZMod.val_natCast_of_lt hq
  have hsub : (x - ((p / 2 : ℕ) : ZMod p)).val =
      if p / 2 ≤ x.val then x.val - p / 2 else p - (p / 2 - x.val) := by
    split_ifs with h
    · simpa [hc] using (ZMod.val_sub (a := x) (b := ((p / 2 : ℕ) : ZMod p)) (by simpa [hc]))
    · have hd := ZMod.val_sub (a := ((p / 2 : ℕ) : ZMod p)) (b := x) (by simp [hc]; omega)
      have he : (((p / 2 : ℕ) : ZMod p) - x) ≠ 0 := by
        intro he
        have := congrArg ZMod.val he
        simp [hd, hc] at this
        omega
      rw [← neg_sub, ZMod.neg_val, if_neg he, hd, hc]
  have hadd : ((((p / 2 : ℕ) : ZMod p) + x)).val =
      if p ≤ p / 2 + x.val then p / 2 + x.val - p else p / 2 + x.val := by
    split_ifs with h
    · simpa [hc] using (ZMod.val_add_of_le (a := ((p / 2 : ℕ) : ZMod p)) (b := x) (by simpa [hc]))
    · simpa [hc] using (ZMod.val_add_of_lt (a := ((p / 2 : ℕ) : ZMod p)) (b := x) (by simp [hc]; omega))
  have h1 : absZ x < absZ (x - ((p / 2 : ℕ) : ZMod p)) := by
    unfold absZ at *
    rw [hsub]
    split_ifs at * <;> omega
  have h2 : absZ x < absZ (((p / 2 : ℕ) : ZMod p) + x) := by
    unfold absZ at *
    rw [hadd]
    split_ifs at * <;> omega
  refine ⟨h1, by simp [decodeResidue, h1], ?_⟩
  have he : (((p / 2 : ℕ) : ZMod p) + x) - ((p / 2 : ℕ) : ZMod p) = x := by abel
  simp [decodeResidue, he, not_lt_of_ge h2.le]

#print axioms solution
