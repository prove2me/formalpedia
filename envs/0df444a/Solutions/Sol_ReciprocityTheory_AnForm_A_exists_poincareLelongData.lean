-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.exists_poincareLelongData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:29.051252+00:00
-- url     : https://prove2.me/submissions/0f5adb74-41b5-40ca-a9d3-ce169e075de7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (z : Fin (n + 1) → ℂ)
    (hz : z ∈ U) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) :
    ∃ v : (Fin (n + 1) → ℂ) → ℝ, PoincareLelongData U v φ ∧ v z = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  let f : ContDiffBump z := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨f, ⟨hU, f.contDiff, f.hasCompactSupport, ?_, hφ⟩,
    f.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))⟩
  rw [f.tsupport_eq]
  exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
end ReciprocityTheory.AnForm.A
