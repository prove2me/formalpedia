-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_X_ce1131bead89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:35.643039+00:00
-- url     : https://prove2.me/submissions/94ff5ced-7619-4c19-b8a5-865ea504b116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable [DecidableEq K] {E : Type*} [Field E]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
theorem _root_.solution (ψ : MRing ι →+* E) (S : Finset K) (p : Σ k, ι k) :
    specMap ψ S (X p) = cS E S p.1 * MvPolynomial.C (ψ (X p)) := aeval_X _ _
end GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
