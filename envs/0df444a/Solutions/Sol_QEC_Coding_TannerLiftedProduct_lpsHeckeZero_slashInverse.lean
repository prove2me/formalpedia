-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeZero_slashInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:11:26.728855+00:00
-- url     : https://prove2.me/submissions/adff9080-f453-4169-8dcb-394b3857d87f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScalarWeightTwo
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeZero_scalarInverse

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] (g : ℍ→ℂ) :
    (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) =
      (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) := by
  rw [lpsHeckeZero_scalarInverse,SlashAction.slash_mul,lpsScalarWeightTwo]
end QEC.Coding.TannerLiftedProduct
