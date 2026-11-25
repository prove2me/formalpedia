-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_isOpen_leftCosetSet_d0ad5d875986
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:46.080502+00:00
-- url     : https://prove2.me/submissions/db96bea4-f6eb-41a5-8930-bd0f02417a4b

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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {K : Subgroup G₂} (hK : IsOpen (K : Set G₂)) (s : G₂) :
    IsOpen (leftCosetSet K s) :=
  hK.preimage (continuous_const_mul s⁻¹)
end GroundTheory.Heights₂.Heights.FiniteCovolume
