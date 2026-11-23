-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_preimage_prod_eq_c1495817f774
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:12.071799+00:00
-- url     : https://prove2.me/submissions/775dd88c-3f46-487c-813f-829a4ef4d8e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume

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
theorem _root_.solution (A : Set G₁) :
    Φ ⁻¹' (A ×ˢ V) = (fun x => (Φ x).1) ⁻¹' A ∩ Φ ⁻¹' (univ ×ˢ V) := by
  ext x
  simp [mem_prod]
end GroundTheory.Heights₂.Heights.FiniteCovolume
