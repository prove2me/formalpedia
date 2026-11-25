-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_isFiniteMeasureOnCompacts_0ebe71c42548
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:55:15.00505+00:00
-- url     : https://prove2.me/submissions/ca83ebc2-0e8e-4d7a-a4b3-dc33c3b9fec9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_apply_9df069ee04c7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution [T2Space G₁] [IsFiniteMeasureOnCompacts μ]
    (hV : IsOpen V) (hVc : IsCompact V) : IsFiniteMeasureOnCompacts (sliceMeasure Φ μ V) := by
  refine ⟨fun A hA => ?_⟩
  rw [sliceMeasure_apply hV hA.isClosed.measurableSet]
  have : IsCompact (Φ ⁻¹' (A ×ˢ V)) :=
    (Homeomorph.isCompact_preimage Φ.toHomeomorph).2 (hA.prod hVc)
  exact this.measure_lt_top
end GroundTheory.Heights₂.Heights.FiniteCovolume
