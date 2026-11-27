-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityProductFormula_proof_e6ca7f5df6e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:19.660228+00:00
-- url     : https://prove2.me/submissions/75b084b6-1125-477a-8270-d13a816eb2c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogNormDivSameOrbit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_norm_div_sameOrbit_414d78e5728f

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityProductFormula
theorem _root_.solution (hPts : regularityPointsSum_holds.Statement) (hVert : VerticalClosedPoints.Statement) :
    RegularityProductFormula.Statement := by
  intro K _ ι _ P f g a hP hf hg hfP hgP
  obtain ⟨R, hRP, hRu, hsum⟩ := hPts K ι P hP
  rw [hVert K ι P f g a R hP hf hg hfP hgP hRP hRu]
  exact (hsum _ fun z z' _ h => log_norm_div_sameOrbit hf hg h).symm
end RegularityProductFormula
end GroundTheory.Heights₂.Heights.Inter
