-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_log_bound_mid
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T07:39:35.145034+00:00
-- url     : https://prove2.me/submissions/c9f54286-4d92-4dc4-aa77-655e0f443ae3

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_to_1e8
import Mathlib

set_option maxRecDepth 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace TaoFivePrimes

/-! ### An elementary comparison: $4\log x \le \sqrt x$ for $x \ge 700$

Rosser–Schoenfeld dispose of the middle range in (3.29) by the elementary
comparison $2/\sqrt x \le 1/(2\log x)$, i.e. $4\log x \le \sqrt x$. We certify
it from $\log 2 < 0.6945$ (itself a six-term partial sum of the exponential
series) via $\log x = 2\log\sqrt x = 2(\log(\sqrt x/32) + \log 32)$ and
$\log t \le t-1$. -/

theorem log_two_lt : Real.log 2 < 1389 / 2000 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
  have h1 : (2 : ℝ) < ∑ i ∈ Finset.range 6, ((1389 / 2000 : ℝ) ^ i / (i.factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have h2 : ∑ i ∈ Finset.range 6, ((1389 / 2000 : ℝ) ^ i / (i.factorial : ℝ)) ≤
      Real.exp (1389 / 2000) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 6
  linarith

theorem log_32_lt : Real.log 32 < 6945 / 2000 := by
  have h : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h]
  linarith [log_two_lt]

theorem four_log_le_sqrt {x : ℝ} (hx : 700 ≤ x) : 4 * Real.log x ≤ Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hsqrt : (1978 / 75 : ℝ) ≤ Real.sqrt x := by
    have h75 : ((1978 / 75 : ℝ)) ^ 2 ≤ 700 := by norm_num
    have h5 : (1978 / 75 : ℝ) ≤ Real.sqrt 700 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr h75
    exact h5.trans (Real.sqrt_le_sqrt hx)
  have h1 : Real.log (Real.sqrt x / 32) ≤ Real.sqrt x / 32 - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hsx (by norm_num))
  have h2 : Real.log (Real.sqrt x / 32) + Real.log 32 = Real.log (Real.sqrt x) := by
    rw [← Real.log_mul (ne_of_gt (div_pos hsx (by norm_num)))
                     (show (32 : ℝ) ≠ 0 by norm_num),
        div_mul_cancel₀ _ (show (32 : ℝ) ≠ 0 by norm_num)]
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (by linarith)]
    ring
  have e1 : 8 * Real.log (Real.sqrt x / 32) ≤ 8 * (Real.sqrt x / 32 - 1) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have e2 : 8 * Real.log 32 < 8 * (6945 / 2000 : ℝ) :=
    mul_lt_mul_of_pos_left log_32_lt (by norm_num)
  calc 4 * Real.log x = 8 * Real.log (Real.sqrt x / 32) + 8 * Real.log 32 := by
        rw [h3, ← h2]
        ring
    _ ≤ 8 * (Real.sqrt x / 32 - 1) + 8 * (6945 / 2000 : ℝ) := by linarith
    _ = Real.sqrt x / 4 + 39560 / 2000 := by ring
    _ ≤ Real.sqrt x := by linarith [hsqrt]

/-! ### From the (4.10) middle-range bound to (3.29)

On $700 \le x \le 10^8$ the bound of Theorem 23 (4.10),
$\prod_{p \le x} \frac{p}{p-1} < e^\gamma \log x + 2e^\gamma/\sqrt x$,
combined with the comparison $4\log x \le \sqrt x$ yields (3.29):
$2e^\gamma/\sqrt x \le e^\gamma/(2\log x)$ and
$e^\gamma\log x + e^\gamma/(2\log x) = e^\gamma\log x(1+\frac{1}{2\log^2 x})$. -/

theorem from_1e8 {x : ℝ} (hx : 700 ≤ x)
    (hB : ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hcomp := four_log_le_sqrt hx
  have hkey : 2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x ≤
      Real.exp Real.eulerMascheroniConstant / (2 * Real.log x) := by
    have h5 : Real.exp Real.eulerMascheroniConstant * (4 * Real.log x) ≤
        Real.exp Real.eulerMascheroniConstant * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hcomp (Real.exp_nonneg _)
    rw [div_le_div_iff₀ hs (by linarith : (0 : ℝ) < 2 * Real.log x)]
    rw [show (2 * Real.exp Real.eulerMascheroniConstant) * (2 * Real.log x)
          = Real.exp Real.eulerMascheroniConstant * (4 * Real.log x) from by ring]
    exact h5
  have hsplit : Real.exp Real.eulerMascheroniConstant * Real.log x *
      (1 + 1 / (2 * (Real.log x) ^ 2)) =
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        Real.exp Real.eulerMascheroniConstant / (2 * Real.log x) := by
    field_simp
  rw [hsplit]
  linarith

/-! ### Sketch: log form of (3.29) on $700 \le x \le 10^8$ via Theorem 23 (4.10)

On $700 \le x \le 10^8$ the bound of Theorem 23 (4.10) of Rosser–Schoenfeld,
combined with the comparison $4\log x \le \sqrt x$, gives the product form
(3.29) of the Rosser–Schoenfeld bound. Taking logarithms — every factor
$p/(p-1)$ is positive, so the sum of logs is the log of the product via
`Real.log_prod` — and splitting the log of the product on the right via
`Real.log_mul` and `Real.log_exp` yields the logarithmic form. -/

theorem solution (x : ℝ) (hx : 700 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have hB := rosser_schoenfeld_product_bound_to_1e8 x (by linarith) hx'
  have h1 := from_1e8 hx hB
  have hf : ∀ p ∈ Nat.primesLE ⌊x⌋₊, 0 < (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have h2 : 2 ≤ p := ((Nat.mem_primesLE.mp hp).2).two_le
    have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast h2
    exact div_pos (by linarith) (by linarith)
  have hne : ∀ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ) / ((p : ℝ) - 1)) ≠ 0 :=
    fun p hp => ne_of_gt (hf p hp)
  have hprod : 0 < ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_pos hf
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hfac : 0 < 1 + 1 / (2 * (Real.log x) ^ 2) := by
    have h2 : (0 : ℝ) ≤ 2 * (Real.log x) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h3 : (0 : ℝ) ≤ 1 / (2 * (Real.log x) ^ 2) := one_div_nonneg.mpr h2
    linarith
  calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1))
      = Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)) :=
        (Real.log_prod hne).symm
    _ < Real.log (Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2))) :=
        Real.log_lt_log hprod h1
    _ = Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
        rw [Real.log_mul (ne_of_gt (mul_pos (Real.exp_pos _) hlx)) (ne_of_gt hfac),
            Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hlx),
            Real.log_exp]

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (x : ℝ) (hx : 700 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
