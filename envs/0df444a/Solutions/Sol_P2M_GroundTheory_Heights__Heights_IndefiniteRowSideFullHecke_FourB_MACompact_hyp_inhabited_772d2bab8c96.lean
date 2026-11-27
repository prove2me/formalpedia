-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_hyp_inhabited_772d2bab8c96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:57.172722+00:00
-- url     : https://prove2.me/submissions/957f6b48-1d25-44f6-b8d3-b8a068e79dc1

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
namespace MACompact
theorem _root_.solution :
    MACompact.Hyp (Set.univ : Set (Fin 1 → ℂ)) 0
      (⇑(⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : Fin 1 → ℂ))) := by
  refine ⟨isOpen_univ, contDiff_const.contDiffOn, ?_, ?_, Set.subset_univ _⟩
  · exact (ContDiffBump.contDiff _).contDiffOn
  · exact ContDiffBump.hasCompactSupport _
end MACompact
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
