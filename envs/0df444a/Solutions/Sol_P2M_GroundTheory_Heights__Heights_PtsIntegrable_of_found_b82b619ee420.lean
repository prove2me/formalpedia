-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegrable_of_found_b82b619ee420
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:10.338649+00:00
-- url     : https://prove2.me/submissions/4463546c-b05f-4e58-af88-c0c706c905db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_finsum_mem_le_finsum_mem_abs_db8835e7e74d

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights
namespace PtsIntegrable
theorem _root_.solution (hAbs : Inter.PtsAbsIntegrable.Statement)
    (hMeas : PtsSumMeasurable.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  refine (hAbs K ι P e Ψ L A s hP hΨ hL hA hs).mono' (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact abs_finsum_mem_le_finsum_mem_abs _ _
end PtsIntegrable
end GroundTheory.Heights₂.Heights
