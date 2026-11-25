-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.two_form_sq_finset_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:52.615857+00:00
-- url     : https://prove2.me/submissions/cbcaa142-e681-4df8-95b3-f6aecabe3ea7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_norm_sum_sq

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
theorem _root_.solution {n N : ℕ} (σ : Fin N → Fin n → Fin n → ℂ) :
    sq2 n (fun j k => ∑ i, σ i j k) ≤ N * ∑ i, sq2 n (σ i) := by
  have h : ∀ j k, ‖∑ i, σ i j k‖ ^ 2 ≤ N * ∑ i, ‖σ i j k‖ ^ 2 := fun j k =>
    loc_norm_sum_sq (fun i => σ i j k)
  have hs : ∑ i, ∑ j, ∑ k, ‖σ i j k‖ ^ 2 = ∑ j, ∑ k, ∑ i, ‖σ i j k‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  simp only [sq2]
  rw [← Finset.sum_div, ← mul_div_assoc, hs, Finset.mul_sum]
  gcongr with j _
  rw [Finset.mul_sum]
  gcongr with k _
  exact h j k
end ReciprocityTheory.L2DbarEstimates.F
