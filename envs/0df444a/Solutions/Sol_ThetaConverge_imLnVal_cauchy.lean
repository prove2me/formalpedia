-- Prove2me | solution 1 for ThetaConverge.imLnVal_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:24:38.635024+00:00
-- url     : https://prove2.me/submissions/578093e1-aead-4157-96c2-be30a9024466

import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Theorems.Thm_ThetaConverge_incr_bound
namespace ThetaGap
end ThetaGap
namespace ThetaValue
end ThetaValue
/-  ThetaConverge.lean -- ANDÚRIL θ-bridge: discharging the two named obligations of
    `ThetaValue.lean` (`ThetaGap.ConvergenceObligation` and `ThetaGap.RateObligation`).

    These are the entire remaining distance between the merged finite `Im L_n` pipeline and
    a purely-kernel-computed value box for `φ(14) = arg Γℝ(1/2+14i) = −7 log π + Λ`.

    ## What is proved here (all axiom-clean: {propext, Classical.choice, Quot.sound}).

      * `imLnVal_succ_sub`  : the exact one-step increment
            `imLnVal x y (n+1) − imLnVal x y n = y·log(1+1/n) − arctan(y/(x+n+1))`  (`n ≥ 1`).
      * `incr_bound`        : the elementary two-sided bound on that increment,
            `|Δ_m| ≤ (|y|(x+1) + |y|³/3)/m²`, GENERAL in real `y` (arctan-odd symmetry),
            proved from `log s ≤ s−1` (both directions) + `ArctanTaylor` cubic corollaries.
      * `imLnVal_cauchy`    : `CauchySeq (imLnVal x y)` -- the increments are `O(1/m²)`-summable,
            so `cauchySeq_of_summable_dist` gives Cauchy, hence convergence in ℝ.
      * `convergence_obligation : ThetaGap.ConvergenceObligation` -- the FULL branch bridge:
            the Cauchy limit `Λ` satisfies both `imLnVal → Λ` and `Γ(z) = ‖Γ(z)‖·exp(I·Λ)`,
            via `Re L_n = log‖GammaSeq z n‖ → log‖Γ z‖`, `Im L_n = imLnVal → Λ`,
            `exp L_n = GammaSeq z n → Γ z`, and uniqueness of limits.  No branch pinning
            beyond the exp identity -- exactly as the obligation was designed to need.
      * `rate_obligation : ThetaGap.RateObligation` -- the explicit `C/n` rate.  The finite
            tail `|imLnVal N − imLnVal n| ≤ 2B/n` (telescope + `sum_Ioo_inv_sq_le`) passes to
            the limit (`le_of_tendsto`) giving `|Λ − imLnVal n| ≤ 2B/n`, `C := 2B`.

    ## Honest note on the rate constant / box width.
    The obligation asks only for a FINITE, EXPLICIT `C`; `C = 2(|y|(x+1)+|y|³/3)` qualifies and
    is what is delivered here.  It is deliberately loose (the `1/m³` cubic-arctan tail is lumped
    into the `1/m²` log-mismatch tail, and `∑_{m≥n} 1/m² ≤ 2/n` is the cheap telescoping bound).
    A tight numeric `φ(14)` box of width ≤ 2e-3 (the driver's ambition) needs many in-kernel
    arctan terms at large `n₀`; that is mechanical throughput, not further mathematics, and is
    orthogonal to closing the obligations.  See `theta_14_box_of_partial` for the honest,
    hypothesis-free consumption at a chosen order.

    conjecture1_proved = False.  The θ-value convergence + rate obligations, kernel-clean.
    NOT a proof of RH.
-/








open Complex Real Filter Topology ThetaValue ThetaGap

namespace ThetaConverge

/-! ### The one-step increment of `imLnVal`. -/

/-- **Increment identity.**  For `n ≥ 1`,
    `imLnVal x y (n+1) − imLnVal x y n = y·log(1+1/n) − arctan(y/(x+n+1))`. -/
theorem imLnVal_succ_sub (x y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    imLnVal x y (n+1) - imLnVal x y n
      = y * Real.log (1 + 1/(n:ℝ)) - Real.arctan (y/(x + (n:ℝ) + 1)) := by
  unfold imLnVal
  rw [Finset.sum_range_succ]
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) = Real.log (1 + 1/(n:ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
  have hlogy : y * Real.log ((n:ℝ)+1) - y * Real.log (n:ℝ) = y * Real.log (1 + 1/(n:ℝ)) := by
    rw [← mul_sub, hlog]
  push_cast [Finset.sum_range_succ]
  rw [show (x + ((n:ℝ) + 1)) = (x + (n:ℝ) + 1) from by ring]
  linarith [hlogy]

/-! ### The elementary two-sided increment bound (general real `y`). -/





/-! ### Convergence: `imLnVal` is Cauchy, hence convergent. -/



/-! ### The complex `L_n` and its bridges to `imLnVal` / `GammaSeq`. -/







/-! ### The convergence obligation (with the branch bridge). -/



/-! ### The rate obligation (explicit `C/n`). -/







/-! ### The payoff: the kernel `φ(14)` box (assembly of both obligations).

    Both obligations discharged, we consume them through `ThetaGap.phi_box_of_rate_and_partial`.
    Ingredients at the operating point `x = 1/4`, `y = 7`, order `n₀ = 1`:
      * `imLnVal (1/4) 7 1 = −(arctan 28 + arctan(28/5)) ∈ [−4, 0]`  (crude rational partial box);
      * `log π ∈ [1, 2]`  (crude rational box; `e < π < e²`);
      * `Γ(1/4+7i) ≠ 0`  (`im = 7 ≠ 0`).
    The resulting `theta_14_box` is a genuine, hypothesis-free, argument-free kernel theorem.

    HONEST WIDTH NOTE.  The interval width is dominated by the rate term `C/n₀` with the loose
    (but valid) constant `C = 2(|y|(x+1)+|y|³/3) ≈ 246` at `n₀ = 1`, so the numeric width here is
    large (~5e2).  Narrowing to the driver's ≈1e-3 ambition is pure per-term arctan-boxing
    throughput at large `n₀` (mechanical `ArctanTaylor.arctan_bracket` iteration) plus a tightened
    `C` — orthogonal to the mathematical content, which is the two obligations proved above. -/









end ThetaConverge


/-  ThetaConverge.lean -- ANDÚRIL θ-bridge: discharging the two named obligations of
    `ThetaValue.lean` (`ThetaGap.ConvergenceObligation` and `ThetaGap.RateObligation`).

    These are the entire remaining distance between the merged finite `Im L_n` pipeline and
    a purely-kernel-computed value box for `φ(14) = arg Γℝ(1/2+14i) = −7 log π + Λ`.

    ## What is proved here (all axiom-clean: {propext, Classical.choice, Quot.sound}).

      * `imLnVal_succ_sub`  : the exact one-step increment
            `imLnVal x y (n+1) − imLnVal x y n = y·log(1+1/n) − arctan(y/(x+n+1))`  (`n ≥ 1`).
      * `incr_bound`        : the elementary two-sided bound on that increment,
            `|Δ_m| ≤ (|y|(x+1) + |y|³/3)/m²`, GENERAL in real `y` (arctan-odd symmetry),
            proved from `log s ≤ s−1` (both directions) + `ArctanTaylor` cubic corollaries.
      * `imLnVal_cauchy`    : `CauchySeq (imLnVal x y)` -- the increments are `O(1/m²)`-summable,
            so `cauchySeq_of_summable_dist` gives Cauchy, hence convergence in ℝ.
      * `convergence_obligation : ThetaGap.ConvergenceObligation` -- the FULL branch bridge:
            the Cauchy limit `Λ` satisfies both `imLnVal → Λ` and `Γ(z) = ‖Γ(z)‖·exp(I·Λ)`,
            via `Re L_n = log‖GammaSeq z n‖ → log‖Γ z‖`, `Im L_n = imLnVal → Λ`,
            `exp L_n = GammaSeq z n → Γ z`, and uniqueness of limits.  No branch pinning
            beyond the exp identity -- exactly as the obligation was designed to need.
      * `rate_obligation : ThetaGap.RateObligation` -- the explicit `C/n` rate.  The finite
            tail `|imLnVal N − imLnVal n| ≤ 2B/n` (telescope + `sum_Ioo_inv_sq_le`) passes to
            the limit (`le_of_tendsto`) giving `|Λ − imLnVal n| ≤ 2B/n`, `C := 2B`.

    ## Honest note on the rate constant / box width.
    The obligation asks only for a FINITE, EXPLICIT `C`; `C = 2(|y|(x+1)+|y|³/3)` qualifies and
    is what is delivered here.  It is deliberately loose (the `1/m³` cubic-arctan tail is lumped
    into the `1/m²` log-mismatch tail, and `∑_{m≥n} 1/m² ≤ 2/n` is the cheap telescoping bound).
    A tight numeric `φ(14)` box of width ≤ 2e-3 (the driver's ambition) needs many in-kernel
    arctan terms at large `n₀`; that is mechanical throughput, not further mathematics, and is
    orthogonal to closing the obligations.  See `theta_14_box_of_partial` for the honest,
    hypothesis-free consumption at a chosen order.

    conjecture1_proved = False.  The θ-value convergence + rate obligations, kernel-clean.
    NOT a proof of RH.
-/








open Complex Real Filter Topology ThetaValue ThetaGap

section
namespace ThetaConverge
end ThetaConverge
open ThetaConverge

/-! ### The one-step increment of `imLnVal`. -/



/-! ### The elementary two-sided increment bound (general real `y`). -/





/-! ### Convergence: `imLnVal` is Cauchy, hence convergent. -/


theorem solution (x y : ℝ) (hx : 0 < x) : CauchySeq (imLnVal x y) := by
  set B : ℝ := |y| * (x+1) + |y| ^3/3 with hB
  apply cauchySeq_of_summable_dist
  rw [← summable_nat_add_iff 1]
  apply Summable.of_nonneg_of_le
    (g := fun n : ℕ => dist (imLnVal x y (n+1)) (imLnVal x y (n+1+1)))
    (f := fun n : ℕ => B / ((n:ℝ)+1)^2)
  · intro n; exact dist_nonneg
  · intro n
    have hn1 : 1 ≤ n+1 := by omega
    rw [Real.dist_eq]
    have hid := imLnVal_succ_sub x y (n+1) hn1
    have hb := incr_bound x y hx (n+1) hn1
    rw [abs_sub_comm]
    push_cast at hid hb ⊢
    rw [hid]
    convert hb using 2
  · have hsum : Summable (fun n : ℕ => B / (n:ℝ)^2) := by
      have : Summable (fun n : ℕ => (1:ℝ) / (n:ℝ)^2) := by
        exact_mod_cast (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa [div_eq_mul_inv, mul_comm] using this.mul_left B
    rw [← summable_nat_add_iff 1] at hsum
    simpa using hsum
