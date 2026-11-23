-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_norm_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:47.629008+00:00
-- url     : https://prove2.me/submissions/b2c98d67-965d-4fb1-ac62-bc4ab3d71305

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA

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
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] {N : ℕ} (a : Fin N → E) :
    ‖∑ i, a i‖ ^ 2 ≤ N * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
  have h2 : (∑ i, ‖a i‖) ^ 2 ≤ N * ∑ i, ‖a i‖ ^ 2 := by
    first
    | (have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
       simpa using h3)
    | (have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i‖)
       simpa using h3)
  calc ‖∑ i, a i‖ ^ 2 ≤ (∑ i, ‖a i‖) ^ 2 := by gcongr
    _ ≤ N * ∑ i, ‖a i‖ ^ 2 := h2
end ReciprocityTheory.L2DbarEstimates.F
