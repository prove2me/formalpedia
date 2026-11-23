-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.sqNorm_entry_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:06.009952+00:00
-- url     : https://prove2.me/submissions/825cddc7-341c-42a0-a32e-ea4d3c50225d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel

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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (σ : Fin n → Fin n → ℂ) (j k : Fin n) : ‖σ j k‖ ^ 2 ≤ 2 * sq2 n σ := by
  unfold sq2
  have e : 2 * ((∑ j, ∑ k, ‖σ j k‖ ^ 2) / 2) = ∑ j, ∑ k, ‖σ j k‖ ^ 2 := by ring
  rw [e]
  calc ‖σ j k‖ ^ 2 ≤ ∑ k', ‖σ j k'‖ ^ 2 :=
        Finset.single_le_sum (f := fun k' => ‖σ j k'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', ‖σ j' k'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ k', ‖σ j' k'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ j)
end ReciprocityTheory.L2DbarEstimates.F
