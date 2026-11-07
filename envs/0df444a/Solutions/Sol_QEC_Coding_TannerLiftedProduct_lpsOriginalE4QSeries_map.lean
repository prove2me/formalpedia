-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4QSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:03.653534+00:00
-- url     : https://prove2.me/submissions/d1387bd5-57d2-4661-b44e-716fe296b221

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalEisensteinQSeries_map

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries 4)=
      qExpansion 1 ModularForm.E₄ :=
  lpsOriginalEisensteinQSeries_map 4 (by decide) ⟨2,rfl⟩
end QEC.Coding.TannerLiftedProduct
