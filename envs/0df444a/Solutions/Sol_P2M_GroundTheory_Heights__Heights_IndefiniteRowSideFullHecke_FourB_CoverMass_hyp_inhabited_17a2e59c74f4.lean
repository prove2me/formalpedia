-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_CoverMass_hyp_inhabited_17a2e59c74f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:45.800069+00:00
-- url     : https://prove2.me/submissions/fbfb7cec-1d9c-4c51-a170-36ab7825d241

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace CoverMass
theorem _root_.solution :
    CoverMass.Hyp (Set.univ : Set (Fin 1 → ℂ)) ∅ id 1 := by
  refine ⟨isOpen_univ, measure_empty, differentiableOn_id, fun x _ => by simp, ?_, ?_⟩
  · refine IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn ?_ ?_ ?_
    · exact isClosed_univ.isClosedMap_subtype_val
    · intro w _
      refine Set.Subsingleton.finite fun a ha b hb => Subtype.ext ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff, id] at ha hb
      rw [ha, hb]
    · exact (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.1
        isOpen_univ.isOpenEmbedding_subtypeVal.isLocalHomeomorph).mono (Set.subset_univ _)
  · intro w _
    have : {x | x ∈ (Set.univ : Set (Fin 1 → ℂ)) ∧ id x = w} = {w} := by ext x; simp
    rw [this, Set.ncard_singleton]
end CoverMass
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
