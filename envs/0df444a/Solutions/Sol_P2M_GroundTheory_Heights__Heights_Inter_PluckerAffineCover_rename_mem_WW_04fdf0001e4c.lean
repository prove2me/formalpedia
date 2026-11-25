-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_rename_mem_WW_04fdf0001e4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:59.392649+00:00
-- url     : https://prove2.me/submissions/79349d28-198b-45b1-9f79-e211a44b524c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_multiConeMap_rename0_a76163a15ff8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wwCoord_comp_1b68d214eb86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_multiConeMap_of_homog_3655d6d60990


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (r : MRing S.YIdx) (b : T.YBlk → ℕ) (hr : IsMultiHomog r b) (h0 : aeval (yyc S) r = 0) :
    rename (T.yyEmb 0) r ∈ S.WW := by
  show rename (T.yyEmb 0) r ∈ RingHom.ker (T.multiConeMap (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)))
  rw [RingHom.mem_ker, multiConeMap_rename0, wwCoord_comp, DiagRAux.multiConeMap_of_homog _ r b hr, h0]
  simp
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
