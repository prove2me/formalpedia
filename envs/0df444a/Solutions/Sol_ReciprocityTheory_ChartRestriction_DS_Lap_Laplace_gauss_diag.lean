-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:41.431507+00:00
-- url     : https://prove2.me/submissions/b72cdadb-d264-41ed-aec3-6a3dfa7365c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
theorem _root_.solution {d : ℕ} (b : Fin d → ℂ) (hb : ∀ i, 0 < (b i).re) :
    ∫ v : Fin d → ℝ, cexp (-∑ i, b i * (v i : ℂ) ^ 2) ≠ 0 := by
  have hb0 : ∀ i, b i ≠ 0 := fun i h => by
    have h' := hb i
    rw [h] at h'
    simp at h'
  have h := GaussianFourier.integral_cexp_neg_sum_mul_add hb (fun _ => (0 : ℂ))
  simp only [zero_mul, Finset.sum_const_zero, add_zero] at h
  rw [h, Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [Ne, Complex.cpow_eq_zero_iff]
  rintro ⟨h1, -⟩
  exact div_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) (hb0 i) h1
end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
