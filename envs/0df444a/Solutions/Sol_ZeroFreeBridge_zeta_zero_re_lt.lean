-- Prove2me | solution 1 for ZeroFreeBridge.zeta_zero_re_lt
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:11.347386+00:00
-- url     : https://prove2.me/submissions/49ea18ef-20ba-42f0-be6e-c4f76cb526ad

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
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







end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 4 — zero location): every ζ-zero in the disk has `Re < σ` (`σ > 1`),
   which discharges the `hother`/`hlt` hypotheses of `dlvp_zeta_region_of_canonical_decomp`.

   A point `ρ` in the divisor support of ζ is a zero (`divisor ≠ 0` ⟹ `analyticOrderAt ≠ 0` ⟹ `ζ ρ = 0`,
   using `AnalyticOnNhd.divisor_apply` + `apply_eq_zero_of_analyticOrderAt_ne_zero`), and ζ has no zeros
   with `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`), so `Re ρ < 1 < σ`.  conjecture1_proved = False.
-/



open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {c₀ ρ : ℂ} {R σ : ℝ} (hσ : 1 < σ)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hρ : ρ ∈ ball c₀ R)
    (hdiv : divisor riemannZeta (ball c₀ R) ρ ≠ 0) :
    ρ.re < σ := by
  have hana : AnalyticOnNhd ℂ riemannZeta (ball c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).mono ball_subset_closedBall
  -- divisor ρ ≠ 0 ⟹ analyticOrderAt ρ ≠ 0
  have hord : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro hord0
    apply hdiv
    rw [hana.divisor_apply hρ, hord0]
    rfl
  -- analyticOrderAt ρ ≠ 0 ⟹ ζ ρ = 0
  have hzero : riemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hord
  -- ζ has no zeros with Re ≥ 1
  by_contra h
  push_neg at h
  exact (riemannZeta_ne_zero_of_one_le_re (by linarith)) hzero
