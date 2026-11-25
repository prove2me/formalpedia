-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_isCompact_leftCosetSet_882460967c4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:44.209161+00:00
-- url     : https://prove2.me/submissions/c9cb4a00-7fcf-4f3c-98fa-42ff711fb87c

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
theorem _root_.solution {K : Subgroup G₂} (hK : IsCompact (K : Set G₂)) (s : G₂) :
    IsCompact (leftCosetSet K s) := by
  have : leftCosetSet K s = (s * ·) '' (K : Set G₂) := by
    rw [Set.image_mul_left]; rfl
  rw [this]
  exact hK.image (continuous_const_mul s)
end GroundTheory.Heights₂.Heights.FiniteCovolume
