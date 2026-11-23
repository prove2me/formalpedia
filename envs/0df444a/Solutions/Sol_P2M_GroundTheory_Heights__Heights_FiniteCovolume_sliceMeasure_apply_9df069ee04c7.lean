-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_apply_9df069ee04c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:52.856337+00:00
-- url     : https://prove2.me/submissions/bcfd80a7-ce40-4902-bb16-a4026b0fc762

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_fst_comp_ffba65d6ed46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_eq_restrict_0ba29adf8ab5

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
theorem _root_.solution (hV : IsOpen V) {A : Set G₁} (hA : MeasurableSet A) :
    sliceMeasure Φ μ V A = μ (Φ ⁻¹' (A ×ˢ V)) := by
  rw [sliceMeasure, Measure.map_apply (measurable_fst_comp Φ) hA,
    measure_preimage_prod_eq_restrict hV]
end GroundTheory.Heights₂.Heights.FiniteCovolume
