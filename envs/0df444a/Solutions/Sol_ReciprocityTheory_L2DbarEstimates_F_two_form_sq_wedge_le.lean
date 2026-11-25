-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.two_form_sq_wedge_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:52.428348+00:00
-- url     : https://prove2.me/submissions/1b451b4e-ba9c-4a72-b79c-7fb38c32e48c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_sq_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (a b : Fin n → ℂ) :
    sq2 n (wedge a b) ≤ 2 * (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
  unfold sq2 wedge
  have h : ∀ j k, ‖a j * b k - a k * b j‖ ^ 2 ≤
      2 * (‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (‖a k‖ ^ 2 * ‖b j‖ ^ 2) := by
    intro j k
    have := cut_sq_sub_le (a j * b k) (a k * b j)
    simpa [mul_pow] using this
  have h2 : ∑ j, ∑ k, ‖a j * b k - a k * b j‖ ^ 2 ≤
      ∑ j, ∑ k, (2 * (‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (‖a k‖ ^ 2 * ‖b j‖ ^ 2)) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h j k
  have e1 : ∑ j, ∑ k, ‖a j‖ ^ 2 * ‖b k‖ ^ 2 = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
    rw [Finset.sum_mul_sum]
  have e2 : ∑ j, ∑ k, ‖a k‖ ^ 2 * ‖b j‖ ^ 2 = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
    rw [Finset.sum_comm, Finset.sum_mul_sum]
  have e3 : ∑ j, ∑ k, (2 * (‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (‖a k‖ ^ 2 * ‖b j‖ ^ 2)) =
      2 * (∑ j, ∑ k, ‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (∑ j, ∑ k, ‖a k‖ ^ 2 * ‖b j‖ ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e3, e1, e2] at h2
  linarith
end ReciprocityTheory.L2DbarEstimates.F
