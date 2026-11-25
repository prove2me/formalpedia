-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointArithIntersection_eq_of_ptOf_eq_smul_c4234cca63a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:19.870287+00:00
-- url     : https://prove2.me/submissions/b02c22ca-c471-4941-96cf-b4311f433623

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_blockFnField_eq_2808a9951dc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ptOf_chart_96d5086227b9


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointArithIntersection
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
variable {T : Type} [Fintype T]
variable {K' : Type} [Field K'] [NumberField K']
namespace GroundTheory.Heights₂.Heights.PointArithIntersection
theorem _root_.solution {y : (Σ _ : Unit, T) → K'} {c : Unit → T} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {φ ψ : blockFnField y →ₐ[ℚ] ℂ} (t : ℂ) (h : ptOf y c φ = fun p => t * ptOf y c ψ p) : φ = ψ := by
  have ht : t = 1 := by
    have := congrFun h ⟨(), c ()⟩
    simp only [ptOf_chart hc, mul_one] at this
    exact this.symm
  subst ht
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (blockFnField_eq y c hc) ?_
  rintro _ ⟨p, rfl⟩
  have := congrFun h p
  simp only [one_mul] at this
  exact this
end GroundTheory.Heights₂.Heights.PointArithIntersection
