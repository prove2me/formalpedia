-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.pi_bound_of_element_yukon_082a13d8a402
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:37.457713+00:00
-- url     : https://prove2.me/submissions/f723bf1f-d104-4556-bdc1-2ba521dfcc5c

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable


import Init
import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1
set_option backward.isDefEq.respectTransparency.types false
namespace Polynomial
end Polynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero Polynomial
section Core
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)
/-- (ii) One element `f` with `ord f = n`, `pole (D f) ≤ T`, `n` a unit in `K`, and
`s ≤ T` force `1 - ord (Dπ) ≤ T + n`. -/
theorem _root_.solution [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s T : ℤ)
    (hsT : s ≤ T) (hint : ∀ u : L, v u ≤ 1 → v (D u) ≤ max (exp s) (v (D π)))
    (f : L) (n : ℕ) (hn : (n : K) ≠ 0) (hf : v f = exp (-(n : ℤ)))
    (hDf : v (D f) ≤ exp T) :
    v (D π) ≤ exp (T + n - 1)  := by
  by_contra hlt
  rw [not_le] at hlt
  have hDπ0 : v (D π) ≠ 0 := (exp_pos.trans hlt).ne'
  have hd : v (D π) = exp (v (D π)).log := (exp_log hDπ0).symm
  rw [hd, exp_lt_exp] at hlt
  have hn1 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hu, hfu⟩ := unit_part v π hπ f (k + 1) hf
  set u := f / π ^ (k + 1)
  have hvn : v ((k + 1 : ℕ) : L) = 1 := by
    rw [← map_natCast (algebraMap K L)]; exact Valuation.IsTrivialOn.eq_one _ hn
  rw [hfu, Derivation.leibniz, Derivation.leibniz_pow] at hDf
  simp only [smul_eq_mul] at hDf
  have hA : v (u * ((k + 1) • (π ^ (k + 1 - 1) * D π))) = exp ((v (D π)).log - k) := by
    rw [v.map_mul, hu, one_mul, nsmul_eq_mul, v.map_mul, hvn, one_mul,
      v.map_mul, v.map_pow, hπ, Nat.add_sub_cancel, exp_neg_one_pow, hd, ← exp_add, log_exp]
    congr 1; ring
  have hB : v (π ^ (k + 1) * D u) < exp ((v (D π)).log - k) := by
    rw [v.map_mul, v.map_pow, hπ, exp_neg_one_pow]
    have h1 := hint u hu.le
    rw [hd] at h1
    refine lt_of_le_of_lt (mul_le_mul_right h1 _) ?_
    rw [mul_max, ← exp_add, ← exp_add]
    apply max_lt <;> rw [exp_lt_exp] <;> push_cast <;> omega
  rw [v.map_add_eq_of_lt_left (by rw [hA]; exact hB), hA, exp_le_exp] at hDf
  push_cast at hlt
  omega
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
