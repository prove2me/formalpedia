-- Prove2me | solution 1 for ZeroFreeBridge.zeta_recentered_canonical_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:46.793874+00:00
-- url     : https://prove2.me/submissions/1b896491-bc0d-457f-99fe-55312378281b

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


/- PHASE 4 (dVP frontier, item 1 — the recentred-ζ CanonicalDecomp): produce the `CanonicalDecomp` of
   `f = ζ(c₀+·)` on `ball 0 R` that `dlvp_zeta_region_of_canonical_decomp` (and `bc_sum_blaschke`) require.

   `bc_sum_blaschke`/`CanonicalDecomp` are centred at `0`, so ζ enters shifted.  Following the corpus
   pattern (`DlvpEntire.zeta_extract_zeros_poles`): `ζ` is analytic on `closedBall c₀ R` (avoiding the
   pole, `zeta_analyticOnNhd_disk`); the shift `w ↦ c₀+w` is analytic and maps `closedBall 0 R` into it,
   so `ζ(c₀+·)` is analytic (hence meromorphic) on `closedBall 0 R`.  Its order is `≠ ⊤` at the centre
   (`ζ(c₀) ≠ 0`, translation-invariant via `meromorphicOrderAt_comp_of_deriv_ne_zero`), hence everywhere
   (connected disk).  `MeromorphicOn.exists_canonicalDecomp` then yields the decomposition.

   conjecture1_proved = False (NOT a proof of RH).
-/



open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hc : 1 < c₀.re) :
    ∃ g : ℂ → ℂ, CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R := by
  have hshift_ana : AnalyticOnNhd ℂ (fun w => c₀ + w) (closedBall 0 R) :=
    fun z _ => analyticAt_const.add analyticAt_id
  have hmaps : Set.MapsTo (fun w => c₀ + w) (closedBall (0 : ℂ) R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    rw [mem_closedBall, Complex.dist_eq, add_sub_cancel_left]
    simpa using hw
  have hζ_ana : AnalyticOnNhd ℂ riemannZeta (closedBall c₀ R) := zeta_analyticOnNhd_disk c₀ R h1
  have hana : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (closedBall 0 R) :=
    hζ_ana.comp hshift_ana hmaps
  have hmero := hana.meromorphicOn
  -- order ≠ ⊤ at the centre 0
  have hc0 : c₀ ∈ closedBall c₀ R := mem_closedBall_self hR.le
  have hord_0 : meromorphicOrderAt (fun w => riemannZeta (c₀ + w)) 0 ≠ ⊤ := by
    have hg0 : AnalyticAt ℂ (fun w => c₀ + w) (0 : ℂ) := analyticAt_const.add analyticAt_id
    have hg0' : deriv (fun w => c₀ + w) (0 : ℂ) ≠ 0 := by rw [deriv_const_add']; simp
    have hcomp : (fun w => riemannZeta (c₀ + w)) = riemannZeta ∘ (fun w => c₀ + w) := rfl
    rw [hcomp, meromorphicOrderAt_comp_of_deriv_ne_zero hg0 hg0']
    simp only [Function.comp, add_zero]
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hζ_ana c₀ hc0).meromorphicAt]
    exact ((hζ_ana c₀ hc0).continuousAt.eventually_ne (zeta_ne_zero_of_one_lt_re c₀ hc)).filter_mono
      nhdsWithin_le_nhds
  -- extend to all points via connectedness
  have hconn : IsConnected (closedBall (0 : ℂ) R) :=
    (convex_closedBall 0 R).isConnected ⟨0, mem_closedBall_self hR.le⟩
  have hord : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt (fun w => riemannZeta (c₀ + w)) u ≠ ⊤ :=
    (hmero.exists_meromorphicOrderAt_ne_top_iff_forall hconn).1
      ⟨⟨0, mem_closedBall_self hR.le⟩, hord_0⟩
  exact hmero.exists_canonicalDecomp hord
