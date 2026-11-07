-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE6QSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:42:24.03249+00:00
-- url     : https://prove2.me/submissions/d388d946-d330-4bf7-9550-06a4112b30a5

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
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries 6)=
      qExpansion 1 ModularForm.E₆ :=
  lpsOriginalEisensteinQSeries_map 6 (by decide) ⟨3,rfl⟩
end QEC.Coding.TannerLiftedProduct
