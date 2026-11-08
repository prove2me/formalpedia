-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:06:42.741207+00:00
-- url     : https://prove2.me/submissions/48b92d3f-cba6-49f1-9267-4010689b4c01

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_conjugate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_of_conjugate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (γ : SL(2,ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 (N*p) ↔
      ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
        lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
          Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by
  constructor
  · exact lpsHeckeIntersection_conjugate N p γ
  · rintro ⟨δ,hδ,he⟩
    exact lpsHeckeIntersection_of_conjugate N p γ δ hδ he
end QEC.Coding.TannerLiftedProduct
