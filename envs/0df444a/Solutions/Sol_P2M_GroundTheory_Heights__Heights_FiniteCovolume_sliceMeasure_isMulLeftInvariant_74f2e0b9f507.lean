-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_isMulLeftInvariant_74f2e0b9f507
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:06.847164+00:00
-- url     : https://prove2.me/submissions/13b53022-9bb6-4175-845f-954424dc1653

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
theorem _root_.solution [μ.IsMulLeftInvariant] (hV : IsOpen V) :
    (sliceMeasure Φ μ V).IsMulLeftInvariant := by
  refine (forall_measure_preimage_mul_iff _).1 fun g A hA => ?_
  rw [sliceMeasure_apply hV (measurable_const_mul g hA), sliceMeasure_apply hV hA]
  have : Φ ⁻¹' (((g * ·) ⁻¹' A) ×ˢ V) =
      (fun x => Φ.symm (g, 1) * x) ⁻¹' (Φ ⁻¹' (A ×ˢ V)) := by
    ext x
    simp [mem_prod]
  rw [this, measure_preimage_mul]
end GroundTheory.Heights₂.Heights.FiniteCovolume
