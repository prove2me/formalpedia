-- Prove2me | solution 1 for ZeroFreeBridge.zeta_zero_count_strip
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:05.37932+00:00
-- url     : https://prove2.me/submissions/9d9e3c20-df98-4c99-ac96-9fef3503ca6a

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_zeta_sphere_bound_strip
/- PHASE 4 (dVP frontier, rung 2 analytic core — ζ zero-count, UNCONDITIONAL): ζ on a disk
   about `2 + iγ`, the Jensen zero-count applied to ζ, and its boundary bound discharged.

   Obligation (ii) of BC-SUM needs the number of ζ-zeros in a disk near the 1-line to be
   `O(log|γ|)`.  Mathlib v4.32's Jensen count `AnalyticOnNhd.sum_divisor_le`
   (`Mathlib.Analysis.Complex.JensenFormula`) has three hypotheses for `f = ζ`:
     * ζ analytic on the closed disk avoiding `s = 1`  — `zeta_analyticOnNhd_disk`;
     * `ζ c ≠ 0`                                       — `zeta_ne_zero_of_one_lt_re`;
     * a boundary bound `‖ζ‖ ≤ M` on the sphere        — `zeta_sphere_bound` (from
       `zeta_strip_bound`).
   `zeta_zero_count_le` wires the first two in (taking the boundary bound); `zeta_sphere_bound`
   supplies the third with an EXPLICIT `M = (‖c‖+R)/(c.re-R-1) + (‖c‖+R)/(c.re-R)` (`O(|γ|)` for
   `c = 2+iγ`); `zeta_zero_count_unconditional` combines them into a hypothesis-free
   `O(log|γ|)` count.

   This discharges the ZERO-COUNT half of obligation (ii).  The remaining core: the
   partial-fraction split ζ'/ζ = Z + E via the `divisor` (obligation (i)) and
   `borel_caratheodory_deriv` bounding `E`.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn

namespace ZeroFreeBridge

/-- ζ is nonzero right of the 1-line (`Re s > 1`) — the `f c ≠ 0` hypothesis of Jensen's
    `sum_divisor_le` at a disk center like `2 + iγ`. -/
theorem zeta_ne_zero_of_one_lt_re (c : ℂ) (hc : 1 < c.re) : riemannZeta c ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (le_of_lt hc)

/-- ζ is analytic on any closed disk that avoids the pole `s = 1` — the `AnalyticOnNhd`
    hypothesis of Jensen's `sum_divisor_le` / `circleAverage_log_norm`. -/
theorem zeta_analyticOnNhd_disk (c : ℂ) (r : ℝ) (h1 : (1 : ℂ) ∉ Metric.closedBall c r) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c r) := by
  have hsub : Metric.closedBall c r ⊆ {(1 : ℂ)}ᶜ := by
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact h1 hs
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun s hs =>
    (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton).mono hsub



/-- **Jensen zero-count for ζ** (boundary bound as a hypothesis). -/
theorem zeta_zero_count_le (c : ℂ) (r R M : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (h1 : (1 : ℂ) ∉ Metric.closedBall c |R|) (hc : 1 < c.re)
    (hbound : ∀ z ∈ Metric.sphere c |R|, ‖riemannZeta z‖ ≤ M) :
    ∑ᶠ u, divisor riemannZeta (Metric.closedBall c |r|) u
      ≤ Real.log (M / ‖riemannZeta c‖) / Real.log (R / r) :=
  (zeta_analyticOnNhd_disk c |R| h1).sum_divisor_le hr hrR hM
    (zeta_ne_zero_of_one_lt_re c hc) hbound



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 3 input — strip-capable Jensen zero count): the version of
   `zeta_zero_count_unconditional` (`DlvpZetaDisk`) that survives the disk DIPPING BELOW `Re = 1`.

   The count `∑ divisor ≤ log(M/‖ζ c‖)/log(R/r)` (`zeta_zero_count_le`) takes the boundary bound `M`
   as a HYPOTHESIS and only needs `1 < c.re` at the CENTER plus `1 ∉ closedBall c |R|` — ζ is
   analytic on ANY disk avoiding `s = 1`, even one reaching `Re < 1`.  The original
   `zeta_zero_count_unconditional` supplies `M` via `zeta_sphere_bound` (`Re > 1`), forcing
   `|R| + 1 < c.re`.  Here we supply `M` via `zeta_strip_bound` (valid on the FULL strip
   `Re > 0`, `s ≠ 1`), so the disk may enclose a nontrivial zero `ρ₀` (`Re < 1`).

   This delivers the `O(L)` zero-count bound `∑ |divisor| ≤ Ccount·L` that `hAL_arith` (`DlvpHALArith`)
   consumes.  conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge




theorem solution (c : ℂ) (r R : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hc1 : 1 < c.re)
    (hRlt : |R| < c.re - 1/2) (himc : |R| + 2 ≤ |c.im|) :
    ∑ᶠ u, divisor riemannZeta (Metric.closedBall c |r|) u
      ≤ Real.log (((‖c‖ + |R|) / (|c.im| - |R|) + (‖c‖ + |R|) / (c.re - |R|)) / ‖riemannZeta c‖)
          / Real.log (R / r) := by
  have hRpos : 0 < |R| := lt_trans hr hrR
  have hcre_norm : c.re ≤ ‖c‖ := Complex.re_le_norm c
  have hd_re : 0 < c.re - |R| := by linarith
  have hd_im : 0 < |c.im| - |R| := by linarith
  have h1notin : (1 : ℂ) ∉ Metric.closedBall c |R| := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    intro hle
    have : |c.im| ≤ ‖c - 1‖ := by
      calc |c.im| = |(c - 1).im| := by rw [Complex.sub_im]; simp
        _ ≤ ‖c - 1‖ := Complex.abs_im_le_norm _
    rw [norm_sub_rev] at this
    linarith
  have hterm2 : 1 ≤ (‖c‖ + |R|) / (c.re - |R|) := by rw [le_div_iff₀ hd_re]; linarith
  have hM : 1 ≤ (‖c‖ + |R|) / (|c.im| - |R|) + (‖c‖ + |R|) / (c.re - |R|) := by
    have : 0 ≤ (‖c‖ + |R|) / (|c.im| - |R|) := by positivity
    linarith
  refine zeta_zero_count_le c r R _ hr hrR hM h1notin hc1 ?_
  intro z hz
  exact zeta_sphere_bound_strip c |R| hRpos hRlt himc hz
