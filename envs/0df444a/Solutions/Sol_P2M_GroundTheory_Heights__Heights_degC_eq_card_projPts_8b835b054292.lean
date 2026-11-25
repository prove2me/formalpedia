-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_degC_eq_card_projPts_8b835b054292
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:30.385891+00:00
-- url     : https://prove2.me/submissions/04c5567e-5387-499d-bd32-f35c6a3f49a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) : Geo.degC P = Nat.card (projPts P) := rfl
end GroundTheory.Heights₂.Heights
