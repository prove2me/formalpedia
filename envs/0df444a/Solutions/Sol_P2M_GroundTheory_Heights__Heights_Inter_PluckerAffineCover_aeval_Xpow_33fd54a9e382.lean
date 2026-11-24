-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:07.694577+00:00
-- url     : https://prove2.me/submissions/81894d36-2eae-4472-96b2-bf972b444652

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_yyc_base_29c3d2390e14

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
theorem _root_.solution (i : S.ι) (d : ℕ) :
    aeval (yyc S) (X ⟨.base, i⟩ ^ d : MRing S.YIdx) = algebraMap S.Ω S.Φ (S.x i ^ d) := by
  rw [map_pow, aeval_X, yyc_base, map_pow]
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
