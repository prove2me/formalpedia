-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_preimage_univ_prod_19221bf5a91f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:11.556005+00:00
-- url     : https://prove2.me/submissions/de294c80-47d1-4008-981e-290730bdfdca

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
theorem _root_.solution (hV : IsOpen V) : MeasurableSet (Φ ⁻¹' (univ ×ˢ V)) :=
  ((isOpen_univ.prod hV).preimage Φ.continuous).measurableSet
end GroundTheory.Heights₂.Heights.FiniteCovolume
