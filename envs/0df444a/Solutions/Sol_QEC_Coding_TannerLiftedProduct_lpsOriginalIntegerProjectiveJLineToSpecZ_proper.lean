-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:07:33.041088+00:00
-- url     : https://prove2.me/submissions/559ec55b-c0d5-4fa0-9f75-85177c3e40d5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_finiteType
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_quasiCompact
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_quasiSeparated
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeExistence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeUniqueness

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    IsProper lpsOriginalIntegerProjectiveJLineToSpecZ := by
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_finiteType
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_quasiCompact
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_quasiSeparated
  exact IsProper.of_valuativeCriterion _ (ValuativeCriterion.iff.mpr
    ⟨lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeExistence,
      lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeUniqueness⟩)
end QEC.Coding.TannerLiftedProduct
