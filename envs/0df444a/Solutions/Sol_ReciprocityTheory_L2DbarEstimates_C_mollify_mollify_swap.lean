-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mollify_mollify_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:05.236387+00:00
-- url     : https://prove2.me/submissions/f1c46958-d271-4942-94a1-efbc790b23aa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegIndep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_integrable
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_hasCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {u : V n → ℂ} (hu : Integrable u) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (x : V n) :
    ∫ w, (moll n s (x - w) : ℂ) * ∫ y, (moll n t (w - y) : ℂ) * u y =
      ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
  obtain ⟨C, hC⟩ := (moll_contDiff n s).continuous.bounded_above_of_compact_support
    (moll_hasCompactSupport n hs)
  have hg : Integrable (fun v : V n => (moll n t v : ℂ)) := (moll_integrable n ht).ofReal
  have hI := hu.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hc : Continuous (fun p : V n × V n => (moll n s (x - p.1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((moll_contDiff n s).continuous.comp (continuous_const.sub continuous_fst))
  set F : V n × V n → ℂ := fun p => (moll n s (x - p.1) : ℂ) *
    (ContinuousLinearMap.mul ℂ ℂ) (u p.2) ((fun v : V n => (moll n t v : ℂ)) (p.1 - p.2)) with hFdef
  have hF : Integrable F (volume.prod volume) := by
    refine (hI.norm.const_mul C).mono' (hc.aestronglyMeasurable.mul hI.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [hFdef, norm_mul]
    gcongr
    have h1 := hC (x - p.1)
    simpa using h1
  calc ∫ w, (moll n s (x - w) : ℂ) * ∫ y, (moll n t (w - y) : ℂ) * u y
      = ∫ w, ∫ y, F (w, y) := by
        congr 1; funext w
        rw [← integral_const_mul]
        congr 1; funext y
        simp only [hFdef, ContinuousLinearMap.mul_apply']
        ring
    _ = ∫ y, ∫ w, F (w, y) := integral_integral_swap hF
    _ = ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
        congr 1; funext y
        rw [← integral_complex_ofReal, ← integral_mul_const]
        congr 1; funext w
        simp only [hFdef, ContinuousLinearMap.mul_apply', Complex.ofReal_mul]
        ring
end ReciprocityTheory.L2DbarEstimates.C
