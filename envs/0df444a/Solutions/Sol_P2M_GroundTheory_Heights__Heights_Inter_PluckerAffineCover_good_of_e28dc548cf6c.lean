-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_good_of_e28dc548cf6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:25.289918+00:00
-- url     : https://prove2.me/submissions/1a51fb11-2bd8-4dea-a0cb-8705da58cdc6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_rename_mem_WW_04fdf0001e4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7


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
theorem _root_.solution {r : MRing S.YIdx} {d : ℕ} (hr : IsWeightedHomogeneous (wt S) r (Pi.single .base d))
    (h0 : aeval (yyc S) r = 0) : Good S r :=
  ⟨Pi.single .base d, (isMultiHomog_iff_weighted r _).2 hr, by simp,
    rename_mem_WW S r _ ((isMultiHomog_iff_weighted r _).2 hr) h0⟩
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
