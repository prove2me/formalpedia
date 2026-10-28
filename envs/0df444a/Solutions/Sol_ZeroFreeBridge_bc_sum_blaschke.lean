-- Prove2me | solution 1 for ZeroFreeBridge.bc_sum_blaschke
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:56.816991+00:00
-- url     : https://prove2.me/submissions/8094dd37-f93f-4323-8038-250972e8c86d

import Mathlib
import Theorems.Thm_ZeroFreeBridge_logDeriv_eq_herglotz_add_entire
import Theorems.Thm_ZeroFreeBridge_norm_correction_sum_le
/- PHASE 4 (dVP frontier, rung 2 COMBINE): the Borel-Caratheodory / Jensen "sum bound"
   step, reduced to its two genuinely-analytic inputs.

   BC-SUM (the sole remaining analytic frontier after rungs 1,3,4,5) is:
       -Re(ζ'/ζ)(s) ≤ A·L - Σ_ρ Re(1/(s-ρ)),   L ~ log|t|.
   The classical (Titchmarsh §3.9) route splits the log-derivative on a disk about `2+iγ`:
       ζ'/ζ(s) = Z + E,   Z = Σ_{ρ near s} 1/(s-ρ)  (Herglotz zero sum),  E = entire part,
   and bounds the entire part `‖E‖ ≤ A·L` via Borel-Caratheodory fed by the crude strip
   bound `|ζ| ≤ C|t|`, with the number of zeros controlled by Jensen.

   `bc_sum_of_split` here is the COMBINE: given that split and `‖E‖ ≤ A·L`, it derives the
   BC-SUM inequality `-Re(ζ'/ζ)(s) ≤ A·L - Re(Z)` — exactly the shape rung 1
   (`hzero_of_herglotz`) and rung 4 (`htwo_of_bound`) consume.  So the WHOLE dVP region now
   reduces to the TWO named analytic inputs below, each backed by a concrete Mathlib API:

     (i)  the partial-fraction SPLIT `ζ'/ζ = Z + E` — Jensen divisor machinery
          (`AnalyticOnNhd.circleAverage_log_norm`, `Mathlib.Analysis.Complex.JensenFormula`);
     (ii) the ENTIRE-PART bound `‖E‖ ≤ A·L` — `borel_caratheodory_deriv`
          (`telperion/examples/borel_caratheodory`) with the zero count from
          `AnalyticOnNhd.sum_divisor_le` (Jensen) and the boundary bound `zeta_strip_bound`.

   Improves the region CONSTANT/rate chain only; NOT a proof of RH.  conjecture1_proved = False.
-/


open Complex

namespace ZeroFreeBridge

/-- **BC-SUM COMBINE.**  From the log-derivative split `w = Z + E` with the entire part
    bounded `‖E‖ ≤ A·L`, the BC-SUM inequality `-Re(w) ≤ A·L - Re(Z)` follows: the real part
    of the bounded entire part costs at most `‖E‖ ≤ A·L`.  (`Z` is the Herglotz zero sum,
    `w = ζ'/ζ(s)`.) -/
theorem bc_sum_of_split (w Z E : ℂ) (AL : ℝ) (hw : w = Z + E) (hE : ‖E‖ ≤ AL) :
    (-w).re ≤ AL - Z.re := by
  have h1 : (-w).re = -Z.re - E.re := by rw [hw]; simp; ring
  have h2 : -E.re ≤ ‖E‖ := le_trans (neg_le_abs E.re) (Complex.abs_re_le_norm E)
  rw [h1]; linarith [h2, hE]



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, BLASCHKE item (d4) capstone): the BC-SUM for the Blaschke split.

   Combines the explicit formula `ζ'/ζ = Z + E` (`DlvpBlaschkeSplitExpand`) with the entire-part
   bound `‖E‖ ≤ A·L` (correction via `DlvpCorrectionBound` (d3) + `‖logDeriv g‖` via item (c)) through
   the rung-2 combine `DlvpBCSum.bc_sum_of_split`, yielding the de la Vallee Poussin BC-SUM:

     `-Re(ζ'/ζ)(z) ≤ A·L − Re(Σ_ρ (divisor ρ)/(z−ρ))`,

   with `Z = Σ_ρ (divisor ρ)/(z−ρ)` the Herglotz zero-sum whose `Re` is `≥ 0` near the line (rung 1),
   hence droppable.  This is the `hzero`/`htwo` input the reduction skeleton (`DlvpZeroSum`/`DlvpPole`/
   `DlvpBCSum` → `ZeroFreeRegion`) consumes to reach `β ≤ 1 − c/log|t|`.  conjecture1_proved = False.
-/




open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R)
    (hf_ana : AnalyticOnNhd ℂ f (ball 0 R)) (hg_ana : AnalyticOnNhd ℂ g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hzne : ∀ u ∈ hfin.toFinset, z ≠ u)
    {Bg AL : ℝ} (hg_bound : ‖logDeriv g z‖ ≤ Bg)
    (hAL : (∑ u ∈ hfin.toFinset, |(divisor f (ball 0 R) u : ℝ)|) / (R - ‖z‖) + Bg ≤ AL) :
    (-(logDeriv f z)).re
      ≤ AL - (∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u)).re := by
  have hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) R := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hdu : divisor f (ball 0 R) u ≠ 0 := fun h => hu (by simp [h])
    exact (divisor f (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hdu)
  have hzR : ‖z‖ < R := by rw [← mem_ball_zero_iff]; exact hz
  set Z : ℂ := ∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u) with hZ
  set Corr : ℂ := ∑ u ∈ hfin.toFinset,
    (divisor f (ball 0 R) u : ℂ) * (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z) with hCorr
  have hw : logDeriv f z = Z + (Corr + logDeriv g z) :=
    logDeriv_eq_herglotz_add_entire hR D hf_ana hg_ana hg_ne hfin hz hzne
  have hCorr_bound :
      ‖Corr‖ ≤ (∑ u ∈ hfin.toFinset, |(divisor f (ball 0 R) u : ℝ)|) / (R - ‖z‖) :=
    norm_correction_sum_le hR (fun u => divisor f (ball 0 R) u) hfin.toFinset hsupp hzR
  have hE : ‖Corr + logDeriv g z‖ ≤ AL :=
    le_trans (norm_add_le _ _) (le_trans (add_le_add hCorr_bound hg_bound) hAL)
  exact bc_sum_of_split (logDeriv f z) Z (Corr + logDeriv g z) AL hw hE
