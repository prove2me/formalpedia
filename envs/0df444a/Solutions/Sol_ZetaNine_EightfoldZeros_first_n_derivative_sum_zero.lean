-- Prove2me | solution 1 for ZetaNine.EightfoldZeros.first_n_derivative_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:35:54.173428+00:00
-- url     : https://prove2.me/submissions/8b177b44-bd1e-4678-adce-cd76de65f7d5

import Definitions.Def_ZetaNine_EightfoldZeros
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
The explicit eightfold-zero repair from `new-linear-form-route-repair-2026-10-02.md`.
The numerator has an eighth-power factor at each positive endpoint `1,...,n`.
Its derivatives through order seven vanish there, as do the genuine iterated
real derivatives of the rational function, whose denominator is nonzero there.
This file makes no sign, nonvanishing, asymptotic or irrationality claim.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace ZetaNine.EightfoldZeros

/-! ## General algebra and calculus lemmas (the proof layer) -/

/-- The multiplicity of a polynomial factor falls by at most the derivative order. -/
theorem power_dvd_iterated_derivative {R : Type*} [CommRing R]
    (p : R[X]) (a : R) (e r : ℕ) (h : (X - C a) ^ e ∣ p) :
    (X - C a) ^ (e - r) ∣ (Polynomial.derivative^[r]) p :=
  Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd r h

/-- An actual repeated zero kills all formal derivatives below its multiplicity. -/
theorem eval_iterated_derivative_zero_of_power_dvd {R : Type*} [CommRing R]
    (p : R[X]) (a : R) (e r : ℕ) (h : (X - C a) ^ e ∣ p) (hr : r < e) :
    ((Polynomial.derivative^[r]) p).eval a = 0 := by
  obtain ⟨q, hq⟩ := power_dvd_iterated_derivative p a e r h
  rw [hq]
  simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hr)]

/-- Below its exponent, every genuine iterated derivative of a centered power is zero. -/
theorem iteratedDeriv_centered_power_zero (a : ℝ) (e r : ℕ) (hr : r < e) :
    iteratedDeriv r (fun t : ℝ => (t - a) ^ e) a = 0 := by
  rw [iteratedDeriv_comp_sub_const r (fun t : ℝ => t ^ e) a]
  simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hr)]

/-- Dividing by a polynomial that is nonzero at the endpoint preserves the
vanishing of all derivatives below the numerator's actual factor multiplicity. -/
theorem iteratedDeriv_quotient_zero_of_power_dvd
    (p q : ℝ[X]) (a : ℝ) (e r : ℕ)
    (hp : (X - C a) ^ e ∣ p) (hq : q.eval a ≠ 0) (hr : r < e) :
    iteratedDeriv r (fun t : ℝ => p.eval t / q.eval t) a = 0 := by
  obtain ⟨g, hg⟩ := hp
  have hfactor : (fun t : ℝ => p.eval t / q.eval t) =
      (fun t : ℝ => (t - a) ^ e) * (fun t : ℝ => g.eval t / q.eval t) := by
    funext t
    simp [hg, mul_div_assoc]
  rw [hfactor]
  have hleft : ContDiffAt ℝ r (fun t : ℝ => (t - a) ^ e) a := by fun_prop
  have hgdiff : ContDiffAt ℝ r (fun t : ℝ => g.eval t) a := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      (g.contDiff_aeval (𝕜 := ℝ) r).contDiffAt
  have hqdiff : ContDiffAt ℝ r (fun t : ℝ => q.eval t) a := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      (q.contDiff_aeval (𝕜 := ℝ) r).contDiffAt
  have hright : ContDiffAt ℝ r (fun t : ℝ => g.eval t / q.eval t) a :=
    hgdiff.div hqdiff hq
  rw [iteratedDeriv_mul (g := fun t : ℝ => g.eval t / q.eval t) hleft hright]
  apply Finset.sum_eq_zero
  intro i hi
  have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedDeriv_centered_power_zero a e i (lt_of_le_of_lt hir hr)]
  simp

/-! ## Applications to the actual repair construction -/

/-- The numerator matches the eighth power of the displayed endpoint product. -/
theorem repairNumerator_eval (n : ℕ) (t : ℝ) :
    (repairNumerator n).eval t = repairScale n *
      (∏ j ∈ Finset.range n, (t - ((j + 1 : ℕ) : ℝ))) ^ 8 := by
  simp [repairNumerator, Finset.prod_pow, Polynomial.eval_prod]

/-- The denominator matches the square of the displayed pole product. -/
theorem repairDenominator_eval (n : ℕ) (t : ℝ) :
    (repairDenominator n).eval t =
      (∏ j ∈ Finset.range (4 * n + 1), (t + (j : ℝ))) ^ 2 := by
  simp [repairDenominator, Finset.prod_pow, Polynomial.eval_prod]

/-- The function is exactly the repaired rational expression displayed in the note. -/
theorem repairFunction_eq_formula (n : ℕ) (t : ℝ) :
    repairFunction n t =
      ((Nat.factorial (4 * n) : ℝ) ^ 2) / ((Nat.factorial n : ℝ) ^ 8) *
      (∏ j ∈ Finset.range n, (t - ((j + 1 : ℕ) : ℝ))) ^ 8 /
      (∏ j ∈ Finset.range (4 * n + 1), (t + (j : ℝ))) ^ 2 := by
  rw [repairFunction, repairNumerator_eval, repairDenominator_eval]
  rfl

/-- This is the actual eighth-order endpoint factor, proved for every `k<n`. -/
theorem eighth_power_dvd_repairNumerator (n k : ℕ) (hk : k < n) :
    (X - C ((k + 1 : ℕ) : ℝ)) ^ 8 ∣ repairNumerator n := by
  exact (Finset.dvd_prod_of_mem
    (fun j : ℕ => (X - C ((j + 1 : ℕ) : ℝ)) ^ 8) (Finset.mem_range.mpr hk)).mul_left _

/-- After `r` formal derivatives at least `8-r` zero multiplicity remains. -/
theorem repairNumerator_derivative_factor (n k r : ℕ) (hk : k < n) :
    (X - C ((k + 1 : ℕ) : ℝ)) ^ (8 - r) ∣
      (Polynomial.derivative^[r]) (repairNumerator n) :=
  power_dvd_iterated_derivative _ _ 8 r (eighth_power_dvd_repairNumerator n k hk)

theorem repairNumerator_derivative_eval_zero (n k r : ℕ) (hk : k < n) (hr : r < 8) :
    ((Polynomial.derivative^[r]) (repairNumerator n)).eval ((k + 1 : ℕ) : ℝ) = 0 :=
  eval_iterated_derivative_zero_of_power_dvd _ _ 8 r
    (eighth_power_dvd_repairNumerator n k hk) hr

/-- There is no pole at any positive real endpoint. -/
theorem repairDenominator_eval_pos (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < (repairDenominator n).eval t := by
  rw [repairDenominator_eval]
  apply sq_pos_of_pos
  apply Finset.prod_pos
  intro j hj
  exact add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg j)

/-- The first `n` terms vanish for every derivative order below eight. -/
theorem repairFunction_iteratedDeriv_zero (n k r : ℕ) (hk : k < n) (hr : r < 8) :
    iteratedDeriv r (repairFunction n) ((k + 1 : ℕ) : ℝ) = 0 := by
  exact iteratedDeriv_quotient_zero_of_power_dvd _ _ _ 8 r
    (eighth_power_dvd_repairNumerator n k hk)
    (ne_of_gt (repairDenominator_eval_pos n _ (Nat.cast_pos.mpr (Nat.succ_pos k)))) hr

/-- In particular, the seventh derivatives in the isolated series vanish exactly. -/
theorem repairFunction_seventh_derivative_zero (n k : ℕ) (hk : k < n) :
    iteratedDeriv 7 (repairFunction n) ((k + 1 : ℕ) : ℝ) = 0 :=
  repairFunction_iteratedDeriv_zero n k 7 hk (by norm_num)

/-- The same all-order endpoint result with the original `1≤j≤n` indexing. -/
theorem repairFunction_derivative_zero_on_endpoints (n j r : ℕ)
    (hj : 1 ≤ j) (hjn : j ≤ n) (hr : r < 8) :
    iteratedDeriv r (repairFunction n) (j : ℝ) = 0 := by
  have hjpos : 0 < j := lt_of_lt_of_le (by norm_num) hj
  have hk : j - 1 < n := lt_of_lt_of_le (Nat.sub_lt hjpos (by norm_num)) hjn
  simpa only [Nat.sub_add_cancel hj] using
    repairFunction_iteratedDeriv_zero n (j - 1) r hk hr

/-! ## Main statement and original seventh-order consequence -/

/-- Every order below eight has exactly zero contribution from the first `n`
summands of the actual repair function.  This is the recommended publication
target; its only premise is the order bound `r<8`. -/
theorem checked_first_n_derivative_sum_zero (n r : ℕ) (hr : r < 8) :
    (∑ k ∈ Finset.range n, iteratedDeriv r (repairFunction n) ((k + 1 : ℕ) : ℝ)) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  exact repairFunction_iteratedDeriv_zero n k r (Finset.mem_range.mp hk) hr

/-- Therefore there is exactly zero contribution from the first `n` summands
of the seventh-derivative series; no convergence or sign assumption is used. -/
theorem first_n_seventh_derivative_sum_zero (n : ℕ) :
    (∑ k ∈ Finset.range n, iteratedDeriv 7 (repairFunction n) ((k + 1 : ℕ) : ℝ)) = 0 :=
  checked_first_n_derivative_sum_zero n 7 (by norm_num)

end ZetaNine.EightfoldZeros

/-! Kernel dependency audit; these commands declare no axioms or theorems. -/

open ZetaNine.EightfoldZeros

theorem solution (n r : ℕ) (hr : r < 8) :
    (∑ k ∈ Finset.range n, iteratedDeriv r (repairFunction n) ((k + 1 : ℕ) : ℝ)) = 0 := by
  exact ZetaNine.EightfoldZeros.checked_first_n_derivative_sum_zero n r hr

#print axioms solution
