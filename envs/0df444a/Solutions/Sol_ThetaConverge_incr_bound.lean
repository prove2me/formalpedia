-- Prove2me | solution 1 for ThetaConverge.incr_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:18:54.043649+00:00
-- url     : https://prove2.me/submissions/9b8c0051-fd0e-4d70-8547-ea536943d0a6

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
import Theorems.Thm_ThetaConverge_arctan_sub_self_abs
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

section
namespace ThetaConverge
end ThetaConverge
open ThetaConverge

/-! ### The one-step increment of `imLnVal`. -/



/-! ### The elementary two-sided increment bound (general real `y`). -/




theorem solution (x y : ℝ) (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) :
    |y * Real.log (1 + 1/(m:ℝ)) - Real.arctan (y/(x + (m:ℝ) + 1))|
      ≤ (|y| * (x+1) + |y| ^3/3) / (m:ℝ)^2 := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  set u : ℝ := y/(x + (m:ℝ) + 1) with hu_def
  have hden : (0:ℝ) < x + (m:ℝ) + 1 := by positivity
  have hlog_up : Real.log (1 + 1/(m:ℝ)) ≤ 1/(m:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := 1 + 1/(m:ℝ)) (by positivity); linarith
  have hlog_lo : 1/((m:ℝ)+1) ≤ Real.log (1 + 1/(m:ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (x := 1/(1 + 1/(m:ℝ))) (by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub] at h
    have he : 1/(1 + 1/(m:ℝ)) = (m:ℝ)/((m:ℝ)+1) := by field_simp
    rw [he] at h
    have h2 : (m:ℝ)/((m:ℝ)+1) - 1 = -(1/((m:ℝ)+1)) := by field_simp; ring
    rw [h2] at h; linarith
  set P : ℝ := Real.log (1 + 1/(m:ℝ)) - 1/(x + (m:ℝ) + 1) with hP_def
  have hP_lo : 0 ≤ P := by
    rw [hP_def]
    have : 1/(x + (m:ℝ) + 1) ≤ 1/((m:ℝ)+1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
    linarith
  have hP_hi : P ≤ (x+1)/(m:ℝ)^2 := by
    rw [hP_def]
    have hstep : Real.log (1 + 1/(m:ℝ)) - 1/(x+(m:ℝ)+1) ≤ 1/(m:ℝ) - 1/(x+(m:ℝ)+1) := by linarith
    have hdiff : 1/(m:ℝ) - 1/(x+(m:ℝ)+1) = (x+1)/((m:ℝ)*(x+(m:ℝ)+1)) := by field_simp; ring
    have hbound : (x+1)/((m:ℝ)*(x+(m:ℝ)+1)) ≤ (x+1)/(m:ℝ)^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
    linarith
  have hfirst_eq : y * Real.log (1 + 1/(m:ℝ)) - u = y * P := by
    rw [hP_def, hu_def]; ring
  have hfirst : |y * Real.log (1 + 1/(m:ℝ)) - u| ≤ |y| * (x+1)/(m:ℝ)^2 := by
    rw [hfirst_eq, abs_mul, abs_of_nonneg hP_lo]
    calc |y| * P ≤ |y| * ((x+1)/(m:ℝ)^2) := by
          apply mul_le_mul_of_nonneg_left hP_hi (abs_nonneg y)
      _ = |y| * (x+1)/(m:ℝ)^2 := by ring
  have hu_abs : |u| ≤ |y|/(m:ℝ) := by
    rw [hu_def, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_left (abs_nonneg y) (by positivity); linarith
  have hsecond : |u - Real.arctan u| ≤ |y| ^3/(3*(m:ℝ)^2) := by
    rw [abs_sub_comm]
    have hcube : |u| ^3/3 ≤ |y| ^3/(3*(m:ℝ)^2) := by
      have hpow : |u| ^3 ≤ (|y|/(m:ℝ))^3 := pow_le_pow_left₀ (abs_nonneg u) hu_abs 3
      have h2 : (|y|/(m:ℝ))^3 = |y| ^3/(m:ℝ)^3 := by rw [div_pow]
      rw [h2] at hpow
      have h3 : |y| ^3/(m:ℝ)^3/3 ≤ |y| ^3/(3*(m:ℝ)^2) := by
        rw [div_div]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
      calc |u| ^3/3 ≤ |y| ^3/(m:ℝ)^3/3 := by linarith
        _ ≤ |y| ^3/(3*(m:ℝ)^2) := h3
    linarith [arctan_sub_self_abs u]
  have hsplit : y * Real.log (1 + 1/(m:ℝ)) - Real.arctan u
      = (y * Real.log (1 + 1/(m:ℝ)) - u) + (u - Real.arctan u) := by ring
  calc |y * Real.log (1 + 1/(m:ℝ)) - Real.arctan u|
      = |(y * Real.log (1 + 1/(m:ℝ)) - u) + (u - Real.arctan u)| := by rw [hsplit]
    _ ≤ |y * Real.log (1 + 1/(m:ℝ)) - u| + |u - Real.arctan u| := abs_add_le _ _
    _ ≤ |y| * (x+1)/(m:ℝ)^2 + |y| ^3/(3*(m:ℝ)^2) := add_le_add hfirst hsecond
    _ = (|y| * (x+1) + |y| ^3/3) / (m:ℝ)^2 := by field_simp
