-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_lintegral_le_075e4d26f535
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:59.763369+00:00
-- url     : https://prove2.me/submissions/1c16f87b-fca1-42e5-93b0-b4fbcb0afdaa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphMass
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞) :
    ∑' k, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑' k, f k x ∂μ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ k ∈ s, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑ k ∈ s, f k x ∂μ := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert k s hk ih =>
          rw [Finset.sum_insert hk]
          simp_rw [Finset.sum_insert hk]
          exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
    _ ≤ ∫⁻ x, ∑' k, f k x ∂μ := lintegral_mono fun x => ENNReal.sum_le_tsum s
end GroundTheory.Heights₂.Heights.LocalGraphMass
