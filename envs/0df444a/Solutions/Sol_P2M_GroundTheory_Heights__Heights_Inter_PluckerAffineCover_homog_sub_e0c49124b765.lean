-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homog_sub_e0c49124b765
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:36.72066+00:00
-- url     : https://prove2.me/submissions/cea1c0a8-7ff3-43c9-9582-72dd087d2b33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover

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
theorem _root_.solution {p q : MRing S.YIdx} {m : T.YBlk → ℕ} (hp : IsWeightedHomogeneous (wt S) p m)
    (hq : IsWeightedHomogeneous (wt S) q m) : IsWeightedHomogeneous (wt S) (p - q) m :=
  (weightedHomogeneousSubmodule ℤ (wt S) m).sub_mem hp hq
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
