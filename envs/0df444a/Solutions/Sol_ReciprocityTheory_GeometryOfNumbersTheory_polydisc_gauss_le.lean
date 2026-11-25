-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.polydisc_gauss_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:56.951554+00:00
-- url     : https://prove2.me/submissions/b37310d9-24e0-4750-92d1-828aa35c3906

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_mean_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {R r : ℝ} (hr : 0 < r) (hrR : r < R) (f : (Fin D → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (a : Fin D → ℝ) :
    ‖f 0‖ ^ 2 * ∏ j, discI (a j) r ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) r, ‖f z‖ ^ 2 * Real.exp (-∑ j, a j * ‖z j‖ ^ 2) := by
  have h := polydisc_mean_le hr hrR f hf (fun j s => Real.exp (-(a j * s ^ 2)))
    (fun j => by fun_prop) (fun j s => (Real.exp_pos _).le)
  have e1 : ∏ j, discI (a j) r =
      ∏ j, ∫ z in Metric.ball (0 : ℂ) r, (fun j s => Real.exp (-(a j * s ^ 2))) j ‖z‖ := rfl
  have e2 : (fun z : Fin D → ℂ => ‖f z‖ ^ 2 * Real.exp (-∑ j, a j * ‖z j‖ ^ 2)) =
      fun z => ‖f z‖ ^ 2 * ∏ j, (fun j s => Real.exp (-(a j * s ^ 2))) j ‖z j‖ := by
    funext z
    simp only [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [e1, e2]
  exact h
end ReciprocityTheory.GeometryOfNumbersTheory
