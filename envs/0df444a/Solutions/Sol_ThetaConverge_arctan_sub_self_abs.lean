-- Prove2me | solution 1 for ThetaConverge.arctan_sub_self_abs
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:17:49.59723+00:00
-- url     : https://prove2.me/submissions/66f0c111-9807-439d-876e-3ab53f2a2f58

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
import Theorems.Thm_ArctanTaylor_arctan_le_self
import Theorems.Thm_ArctanTaylor_self_sub_cube_le_arctan
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


theorem solution (u : ℝ) : |Real.arctan u - u| ≤ |u|^3/3 := by
  rcases le_or_gt 0 u with hu | hu
  · have h1 : Real.arctan u ≤ u := ArctanTaylor.arctan_le_self hu
    have h2 : u - u^3/3 ≤ Real.arctan u := ArctanTaylor.self_sub_cube_le_arctan hu
    rw [abs_of_nonneg hu, abs_le]; refine ⟨by linarith, ?_⟩
    have : (0:ℝ) ≤ u^3/3 := by positivity
    linarith
  · have hnu : 0 ≤ -u := by linarith
    have h1 : Real.arctan (-u) ≤ -u := ArctanTaylor.arctan_le_self hnu
    have h2 : (-u) - (-u)^3/3 ≤ Real.arctan (-u) := ArctanTaylor.self_sub_cube_le_arctan hnu
    rw [Real.arctan_neg] at h1 h2
    rw [abs_of_neg hu, abs_le]
    refine ⟨?_, ?_⟩
    · have : (0:ℝ) ≤ (-u)^3/3 := by positivity
      nlinarith [h1, h2]
    · nlinarith [h1, h2]
