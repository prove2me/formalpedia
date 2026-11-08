-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionRepresentative_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:07:51.471215+00:00
-- url     : https://prove2.me/submissions/5fc310c9-2f55-4c1f-a01a-8551adaed412

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionRepresentative_index
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightFactorGL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_spec


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    ∃δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsHeckeIntersectionRepresentative N p hNp i : SL(2,ℤ))⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p i := by
  obtain ⟨δ,hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp
    (lpsHeckeIntersectionRepresentative N p hNp i : SL(2,ℤ))⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem
      (lpsHeckeIntersectionRepresentative N p hNp i).property) none
  rw [lpsHeckeIntersectionRepresentative_index] at he
  exact ⟨δ,hδ,lpsHeckeRightFactorGL ℝ p _ _ _ _ he⟩
end QEC.Coding.TannerLiftedProduct
