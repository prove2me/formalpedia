-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateRepresentative_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:08:08.524584+00:00
-- url     : https://prove2.me/submissions/997e0ef5-d198-4f8b-89fa-64a1ee98dfb4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateRepresentative_index
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
      lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsHeckeConjugateRepresentative N p hNp i : SL(2,ℤ))⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p i := by
  obtain ⟨δ,hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp
    (lpsHeckeConjugateRepresentative N p hNp i : SL(2,ℤ))⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem
      (lpsHeckeConjugateRepresentative N p hNp i).property)
    (some ⟨0,(Fact.out:p.Prime).pos⟩)
  rw [lpsHeckeConjugateRepresentative_index] at he
  exact ⟨δ,hδ,lpsHeckeRightFactorGL ℝ p _ _ _ _ he⟩
end QEC.Coding.TannerLiftedProduct
