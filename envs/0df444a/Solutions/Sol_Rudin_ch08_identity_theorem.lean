-- Prove2me | solution 1 for Rudin.ch08_identity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T20:21:14.480981+00:00
-- url     : https://prove2.me/submissions/4e71ec30-32ae-400f-a168-0c50ee407365

import Mathlib
import Definitions.Def_Rudin_ch03_series
set_option autoImplicit false
open Filter Topology Rudin

lemma scout_hasPowerSeries (a : ℕ → ℝ) (R : ℝ) (hR : 0 < R) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => a n * x ^ n) (f x)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℝ a) 0 (ENNReal.ofReal R) := by
  have hsum (x : ℝ) (hx : |x| < R) : HasSum (fun n => a n * x ^ n) (f x) := by
    obtain ⟨w, hxw, hwR⟩ := exists_between hx
    have hw : 0 < w := (abs_nonneg x).trans_lt hxw
    have hc := (hf w (by rwa [abs_of_pos hw])).cauchySeq
    have hs : Summable (fun n => a n * x ^ n) :=
      summable_powerSeries_of_norm_lt hc (by simpa [Real.norm_eq_abs, abs_of_pos hw] using hxw)
    exact hs.hasSum_iff_tendsto_nat.mpr (hf x hx)
  refine ⟨?_, by simpa using hR, ?_⟩
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hrR : (r : ℝ) < R := by simpa using hr
    apply FormalMultilinearSeries.le_radius_of_tendsto
    have ht := (hsum r (by simpa using hrR)).summable.tendsto_atTop_zero.norm
    simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using ht
  · intro x hx
    have hxR : |x| < R := by simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hx
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hsum x hxR
theorem solution (a b : ℕ → ℝ) (R : ℝ) (hR : 0 < R) (f g : ℝ → ℝ)
    (hf : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => a n * x ^ n) (f x))
    (hg : ∀ x : ℝ, |x| < R → SeriesConvergesTo (fun n => b n * x ^ n) (g x))
    (E : Set ℝ) (hE : E ⊆ Set.Ioo (-R) R) (hagree : ∀ x ∈ E, f x = g x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo (-R) R) (hlim : x₀ ∈ closure (E \ {x₀})) :
    ∀ n, a n = b n := by
  have hfa := scout_hasPowerSeries a R hR f hf
  have hga := scout_hasPowerSeries b R hR g hg
  have hball : Metric.eball (0 : ℝ) (ENNReal.ofReal R) = Set.Ioo (-R) R := by
    ext x
    simp [Metric.mem_eball, edist_dist, Real.dist_eq, abs_lt]
  have hfe : AnalyticOnNhd ℝ f (Set.Ioo (-R) R) := hball ▸ hfa.analyticOnNhd
  have hge : AnalyticOnNhd ℝ g (Set.Ioo (-R) R) := hball ▸ hga.analyticOnNhd
  have heq : Set.EqOn f g (Set.Ioo (-R) R) :=
    hfe.eqOn_of_preconnected_of_mem_closure hge (convex_Ioo (-R) R).isPreconnected hx₀
      ((closure_mono (Set.diff_subset_diff_left (fun x hx => hagree x hx))) hlim)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-R) R := by constructor <;> linarith
  have hevent : f =ᶠ[𝓝 0] g :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hzero) heq
  have hp := hfa.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    hga.hasFPowerSeriesAt hevent
  exact congrFun (FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ hp)
#print axioms solution
