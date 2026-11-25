-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isPsh_logmax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:10:45.249862+00:00
-- url     : https://prove2.me/submissions/a3cc5894-7390-4f04-ad7f-a4fd26c58371

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology Real
private theorem log_max_norm_le_circleAverage_of_analyticOnNhd {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    Real.log (max ‖h 0‖ 1) ≤ Real.circleAverage (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 := by
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI : CircleIntegrable (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hh.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  rcases le_or_gt ‖h 0‖ 1 with h0 | h0
  · rw [max_eq_right h0, Real.log_one]
    have := Real.circleAverage_mono (circleIntegrable_const (0 : ℝ) 0 1) hI
      (fun x _ => Real.log_nonneg (le_max_right _ _))
    rwa [Real.circleAverage_const] at this
  · have hne : h 0 ≠ 0 := by intro e; rw [e, norm_zero] at h0; linarith
    have hh' : AnalyticOnNhd ℂ h (closedBall 0 |1|) := by rwa [abs_one]
    rw [max_eq_left h0.le]
    have hJ := AnalyticOnNhd.circleAverage_log_norm (c := 0) (R := 1) one_ne_zero hh' hne
    have hdn := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh'
    have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor h (closedBall 0 |1|)) u : ℝ) *
        Real.log (1 * ‖0 - u‖⁻¹) := by
      apply finsum_nonneg
      intro u
      by_cases hu : u ∈ closedBall (0 : ℂ) |1|
      · apply mul_nonneg
        · exact_mod_cast hdn u
        · rw [one_mul, zero_sub, norm_neg, Real.log_inv]
          rw [abs_one, mem_closedBall, dist_zero_right] at hu
          exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg u) hu)
      · have hz : (MeromorphicOn.divisor h (closedBall 0 |1|)) u = 0 := by
          by_contra hz
          exact hu ((MeromorphicOn.divisor h _).supportWithinDomain hz)
        rw [hz]; simp
    have hlog : CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 :=
      circleIntegrable_log_norm_meromorphicOn (fun x hx => (hh x (hs hx)).meromorphicAt)
    calc Real.log ‖h 0‖ ≤ Real.circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by
          rw [hJ]; linarith
      _ ≤ _ := Real.circleAverage_mono hlog hI (fun x _ => by
          by_cases hx0 : h x = 0
          · simp [hx0]
          · exact Real.log_le_log (norm_pos_iff.2 hx0) (le_max_left _ _))
end ReciprocityTheory.ChartRestriction.G.Geo
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology Real
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {f : (Fin D → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ReciprocityTheory.AnForm.A.IsPsh U (fun z => Real.log (max ‖f z‖ ε)) := by
  refine ⟨?_, fun z w hdisc => ?_⟩
  · exact ContinuousOn.upperSemicontinuousOn (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm hf.continuousOn) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right hε).ne'))
  set g : ℂ → ℂ := fun ζ => (ε : ℂ)⁻¹ * f (z + ζ • w) with hg
  have hga : AnalyticOnNhd ℂ g (closedBall 0 1) := by
    intro ζ hζ
    have hz : z + ζ • w ∈ U := hdisc ζ (by simpa using hζ)
    have hφ : AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hc : AnalyticAt ℂ (fun ζ : ℂ => f (z + ζ • w)) ζ :=
      AnalyticAt.comp (g := f) (f := fun ζ : ℂ => z + ζ • w) (hf _ hz) hφ
    exact analyticAt_const.mul hc
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI2 : CircleIntegrable (fun ζ => Real.log (max ‖g ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hga.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  have hkey : ∀ ζ : ℂ, Real.log (max ‖f (z + ζ • w)‖ ε) = Real.log ε + Real.log (max ‖g ζ‖ 1) := by
    intro ζ
    have hnorm : ‖g ζ‖ = ‖f (z + ζ • w)‖ / ε := by
      simp only [hg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [div_eq_inv_mul]
    rw [hnorm, ← Real.log_mul hε.ne' (lt_max_of_lt_right one_pos).ne', mul_max_of_nonneg _ _ hε.le,
      show ε * (‖f (z + ζ • w)‖ / ε) = ‖f (z + ζ • w)‖ by field_simp, mul_one]
  have hfun : (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) =
      fun ζ => Real.log ε + Real.log (max ‖g ζ‖ 1) := funext hkey
  refine ⟨?_, ?_⟩
  · show CircleIntegrable (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun]
    exact (circleIntegrable_const _ _ _).add hI2
  · show Real.log (max ‖f z‖ ε) ≤ Real.circleAverage (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun, Real.circleAverage_fun_add (circleIntegrable_const _ _ _) hI2, Real.circleAverage_const]
    have h0 := hkey 0
    simp only [zero_smul, add_zero] at h0
    rw [h0]
    linarith [log_max_norm_le_circleAverage_of_analyticOnNhd hga]
end ReciprocityTheory.ChartRestriction.G.Geo
