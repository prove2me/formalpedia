-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:26.757051+00:00
-- url     : https://prove2.me/submissions/3c8ee1f1-0546-4d5c-9ba7-a2c1365acd69

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_conjugateMatrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightFactorGL


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N*p)) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by
  obtain ⟨δ,hδ,he⟩ := lpsHeckeIntersection_conjugateMatrix N p γ hγ
  exact ⟨δ,hδ,lpsHeckeRightFactorGL ℝ p none none γ δ he⟩
end QEC.Coding.TannerLiftedProduct
