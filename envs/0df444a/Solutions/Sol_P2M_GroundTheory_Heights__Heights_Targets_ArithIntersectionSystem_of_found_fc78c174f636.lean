-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ArithIntersectionSystem_of_found_fc78c174f636
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:24.529981+00:00
-- url     : https://prove2.me/submissions/d55f98cd-6d26-46d3-8c6a-ecd60ebe3be5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIMultilin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ArithSystem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ArithIntersectionSystem_multilin_of_isFamily_a3118908cb91

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem
namespace GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem
theorem _root_.solution (hE : GroundTheory.Heights₂.Heights.Inter.ThmIExists.Statement) (hPF : PFCoordStatement)
    (hCM : ContractMixedStatement) : ArithIntersectionSystemStatement := by
  obtain ⟨I, hI⟩ := (hE : ExistsStatement)
  exact ⟨I, hI, multilin_of_isFamily hI, hPF I hI, hCM I hI⟩
end GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem
