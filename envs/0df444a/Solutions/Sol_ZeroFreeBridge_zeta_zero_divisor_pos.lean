-- Prove2me | solution 1 for ZeroFreeBridge.zeta_zero_divisor_pos
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:01.343624+00:00
-- url     : https://prove2.me/submissions/0578f3f3-ff95-4d86-90eb-5e318b63f7a6

import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
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







end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the SELF-CONTAINED zero-free region): drop the multiplicity hypothesis.

   `dlvp_zeta_region_rate_effective` takes the zero's multiplicity `k` (with `1 ≤ k`) as input.
   `zeta_zero_divisor_pos` derives `1 ≤ divisor ζ (ball c₀ R) ρ₀` directly from `ζ ρ₀ = 0`
   (`analyticOrderAt ≥ 1` at a zero, finite because ζ is not locally zero on the connected disk —
   `ζ c₀ ≠ 0` at the centre `Re c₀ > 1`).  Feeding this in gives the fully self-contained region

     `riemannZeta_ne_zero_region` :  `55/16 ≤ |γ|` ∧ `1 - dlvpRateC/log|γ| < β`  ⟹  `ζ(β+iγ) ≠ 0`,

   i.e. `ζ(s) ≠ 0` on `Re s > 1 - dlvpRateC/log|Im s|` (for `|Im s| ≥ 55/16`), with `dlvpRateC` the
   EXPLICIT effective constant.  The `β ≥ 3/4` restriction of the rate theorem is discharged here:
   `dlvpRateC ≤ 1/1792` and `log|γ| ≥ 1`, so `1 - dlvpRateC/log|γ| > 3/4`, hence any zero in the
   region already has `β > 3/4`; and `β < 1` since ζ has no zeros with `Re ≥ 1`.

   conjecture1_proved = False (NOT a proof of RH — a kernel-verified reduction; it says a zero in the
   region cannot exist, which is what dVP gives, not a proof that ζ's zeros lie on the line).
-/




open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {c₀ ρ₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hc : 1 < c₀.re)
    (hρ : ρ₀ ∈ ball c₀ R) (hzero : riemannZeta ρ₀ = 0) :
    1 ≤ divisor riemannZeta (ball c₀ R) ρ₀ := by
  have hana : AnalyticOnNhd ℂ riemannZeta (ball c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).mono ball_subset_closedBall
  have hmero := hana.meromorphicOn
  have hc0mem : c₀ ∈ ball c₀ R := mem_ball_self hR
  have hconn : IsConnected (ball c₀ R) := (convex_ball c₀ R).isConnected ⟨c₀, hc0mem⟩
  have hord_c0 : meromorphicOrderAt riemannZeta c₀ ≠ ⊤ := by
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero c₀ hc0mem)]
    exact ((hana c₀ hc0mem).continuousAt.eventually_ne
      (zeta_ne_zero_of_one_lt_re c₀ hc)).filter_mono nhdsWithin_le_nhds
  have hord : meromorphicOrderAt riemannZeta ρ₀ ≠ ⊤ :=
    (hmero.exists_meromorphicOrderAt_ne_top_iff_forall hconn).1 ⟨⟨c₀, hc0mem⟩, hord_c0⟩ ⟨ρ₀, hρ⟩
  have hordne : analyticOrderAt riemannZeta ρ₀ ≠ 0 := (hana ρ₀ hρ).analyticOrderAt_ne_zero.mpr hzero
  have ha_ne_top : analyticOrderAt riemannZeta ρ₀ ≠ ⊤ := by
    intro htop
    rw [(hana ρ₀ hρ).meromorphicOrderAt_eq, htop, ENat.map_top] at hord
    exact hord rfl
  rw [hana.divisor_apply hρ]
  lift analyticOrderAt riemannZeta ρ₀ to ℕ using ha_ne_top with n
  have hn0 : n ≠ 0 := by rintro rfl; exact hordne (by simp)
  rw [ENat.map_coe, WithTop.untop₀_coe]
  omega
