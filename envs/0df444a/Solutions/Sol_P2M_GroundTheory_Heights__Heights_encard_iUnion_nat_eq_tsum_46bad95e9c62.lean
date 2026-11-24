-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_encard_iUnion_nat_eq_tsum_46bad95e9c62
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:36.781651+00:00
-- url     : https://prove2.me/submissions/738a2524-0648-419c-9dfa-07d83a7056b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaMultiplicity

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
open MeasureTheory Module Set Filter Function
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Disjoint on s)) :
    (((⋃ n, s n).encard : ℕ∞) : ℝ≥0∞) = ∑' n, (((s n).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]
end GroundTheory.Heights₂.Heights
