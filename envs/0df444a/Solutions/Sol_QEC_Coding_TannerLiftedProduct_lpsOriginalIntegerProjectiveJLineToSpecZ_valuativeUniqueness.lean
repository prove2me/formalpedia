-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeUniqueness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:02:09.311908+00:00
-- url     : https://prove2.me/submissions/39d60819-4cc1-4736-a4c5-0ee4940bc2b2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJ_fraction_precompose_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    ValuativeCriterion.Uniqueness lpsOriginalIntegerProjectiveJLineToSpecZ := by
  intro S
  refine ⟨fun l₁ l₂ => CommSq.LiftStruct.ext ?_⟩
  apply lpsOriginalIntegerProjectiveJ_fraction_precompose_injective S.R S.K
  exact l₁.fac_left.trans l₂.fac_left.symm
end QEC.Coding.TannerLiftedProduct
