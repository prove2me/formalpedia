-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityFormula_proof_e4b68408e909
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:43.05066+00:00
-- url     : https://prove2.me/submissions/f404c27e-6d44-4d75-a059-519db40bf799

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemRegRingSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreBis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CardQuotEqNatAbsNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisSide
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_index_thm


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
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityFormula
theorem _root_.solution (hN : RegularityFunctionFieldNumber.Statement) (hO : RegularityOrder.Statement)
    (hL : RegularityLocal.Statement) : RegularityFormula.Statement := by
  classical
  intro K _ ι _ P b hP hb hbW
  obtain ⟨hF, hNF⟩ := hN K ι P hP
  let _ := hF.toField
  have := hNF
  obtain ⟨hfree, hfin, hrank⟩ := hO K ι P hP
  let b' : regRing P := ⟨b, hbW⟩
  have hb' : b' ≠ 0 := fun h => hb (congrArg Subtype.val h)
  obtain ⟨hfs, hsum⟩ := hL K ι P b' hP hb'
  refine ⟨hfs, hsum.trans ?_⟩
  have hI := (ReciprocityTheory.ChartRestriction.G.AI.index_thm (funField P) (regRing P) hfree hfin (hrank hF) b' hb').2
  exact hI.trans (finsum_eq_sum_of_fintype _).symm
end RegularityFormula
end GroundTheory.Heights₂.Heights.Inter
