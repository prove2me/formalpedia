-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_encard_iUnion_disjoint_nat_d23692977ca6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:32:10.1143+00:00
-- url     : https://prove2.me/submissions/d77cf9a6-1296-4b81-9fa6-f00cd2d76115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeAreaFormula

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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Function.onFun Disjoint s)) :
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) = ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]
end GroundTheory.Heights₂.Heights
