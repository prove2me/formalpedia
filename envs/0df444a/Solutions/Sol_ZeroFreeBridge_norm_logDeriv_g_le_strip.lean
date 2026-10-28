-- Prove2me | solution 1 for ZeroFreeBridge.norm_logDeriv_g_le_strip
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:05:16.239122+00:00
-- url     : https://prove2.me/submissions/99453e02-9e8d-48c0-a038-afaec69a3ed2

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_g_sphere_log_osc_strip
import Theorems.Thm_ZeroFreeBridge_norm_logDeriv_le_of_sphere_log_norm_le_interior
/- PHASE 4 (dVP frontier, ζ boundary growth — LOWER BOUND): a uniform lower bound on |ζ|
   at Re s = 2, the missing lower half of the ζ-growth sphere input.

   The composition `DlvpBoundaryDecomp.norm_logDeriv_le_of_boundary_split` needs, on the sphere,
   `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ`; the upper half is `zeta_sphere_bound`, the lower half is a POSITIVE
   lower bound `‖ζ c‖ ≥ c₀`.  Centering the dVP disk at `Re c = 2` makes this an absolute constant:

     `2 - π²/6 ≤ ‖ζ(s)‖`   for   `2 ≤ Re s`   (and `2 - π²/6 > 0`).

   Proof: `ζ(s) = ∑ₙ 1/(n+1)^s = 1 + T` (Dirichlet series, `n=0` term is `1`); reverse triangle
   `‖ζ‖ ≥ 1 - ‖T‖`; `‖T‖ ≤ ∑ₙ 1/(n+2)^{Re s} ≤ ∑ₙ 1/(n+2)² = π²/6 - 1` (termwise since `Re s ≥ 2`,
   the tail of Basel `hasSum_zeta_two`); so `‖ζ‖ ≥ 1 - (π²/6 - 1) = 2 - π²/6`.  conjecture1_proved = False.
-/


open Complex

namespace ZeroFreeBridge





/-- The constant is positive: `0 < 2 - π²/6`  (since `π < 3.15 ⟹ π² < 9.93 < 12`). -/
theorem two_sub_pi_sq_div_six_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, brick 3 — strip-capable ζ boundary oscillation): the version of
   `zeta_sphere_log_bound` / `g_sphere_log_osc` that survives the sphere DIPPING BELOW `Re = 1`.

   The original `zeta_sphere_log_bound` (`DlvpZetaSphereLog`) needs `R + 1 < c.re`, so the whole
   sphere stays in `Re > 1` — but then the disk cannot enclose a nontrivial zero `ρ₀` (which has
   `Re < 1`).  The KEY observation: `zeta_strip_bound` (`StripBound`) already holds on ALL of
   `stripDomain = {Re > 0} \ {1}` (NOT just `Re > 1`) — so the upper bound `‖ζ z‖ ≤ ‖z‖/‖z-1‖ +
   ‖z‖/Re z` is available on the sub-1 strip too.  We relax the hypothesis to `R < c.re - 1/2`
   (sphere stays in `Re > 1/2 > 0`) plus `R + 2 ≤ |c.im|` (sphere stays off `s = 1`, and `‖z-1‖`
   is large), and — since `ζ` MAY now vanish on the sphere — handle `Real.log ‖ζ z‖` at a zero by
   `Real.log 0 = 0 ≤ log U''` (the upper constant `U'' ≥ 1`).  The oscillation bound is unchanged
   in spirit: `log‖ζ z‖ - log‖ζ c‖ ≤ log U'' - log(2 - π²/6) = O(log|c|) = O(L)`.

   conjecture1_proved = False (NOT a proof of RH).
-/






open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge






theorem solution {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hRlt : R < c₀.re - 1/2) (himc : R + 2 ≤ |c₀.im|)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont : ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R))
    (hg_cont : ContinuousOn g (sphere 0 R))
    (hg_dcc : DiffContOnCl ℂ g (ball 0 R)) (hg_ne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0)
    (hfg0 : ‖riemannZeta c₀‖ ≤ ‖g 0‖) {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * (Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
              - Real.log (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by
  have hd_re : 0 < c₀.re - R := by linarith
  have hd_im : 0 < |c₀.im| - R := by linarith
  have hcre : c₀.re ≤ ‖c₀‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm c₀)
  have hU1 : (1 : ℝ) ≤ (‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R) := by
    have ht1 : (0 : ℝ) ≤ (‖c₀‖ + R) / (|c₀.im| - R) := by positivity
    have ht2 : (1 : ℝ) ≤ (‖c₀‖ + R) / (c₀.re - R) := by rw [le_div_iff₀ hd_re]; linarith
    linarith
  have hAζpos : 0 < Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
      - Real.log (2 - Real.pi ^ 2 / 6) := by
    have h1 : 0 ≤ Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R)) :=
      Real.log_nonneg hU1
    have h2 : Real.log (2 - Real.pi ^ 2 / 6) < 0 :=
      Real.log_neg two_sub_pi_sq_div_six_pos (by nlinarith [Real.pi_gt_three])
    linarith
  have hρ : ‖z₀ - 0‖ < R := by rwa [sub_zero]
  exact norm_logDeriv_le_of_sphere_log_norm_le_interior hAζpos hρ hg_dcc hg_ne
    (g_sphere_log_osc_strip hR hc2 hRlt himc D hf_cont hg_cont hfg0)
