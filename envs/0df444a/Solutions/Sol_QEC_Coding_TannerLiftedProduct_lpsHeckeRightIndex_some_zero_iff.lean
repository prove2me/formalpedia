-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_some_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:06.594285+00:00
-- url     : https://prove2.me/submissions/d7c72d0f-2846-426c-b304-450199cd06ad

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_factorMatrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_of_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightFactorGL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_spec


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    lpsHeckeRightIndex N p hNp γ hγ (some ⟨0,(Fact.out:p.Prime).pos⟩)=
        some ⟨0,(Fact.out:p.Prime).pos⟩ ↔
      γ ∈ lpsHeckeConjugateIntersection N p := by
  constructor
  · intro hi
    obtain ⟨δ,_hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ _
    rw [hi] at he
    exact lpsHeckeConjugateIntersection_of_factor N p γ δ hγ
      (lpsHeckeRightFactorGL ℝ p _ _ γ δ he)
  · intro hγ'
    obtain ⟨δ,_hδ,he⟩ := lpsHeckeConjugateIntersection_factorMatrix N p γ hγ'
    exact lpsHeckeRightIndex_of_factor N p hNp γ hγ _ _ δ he
end QEC.Coding.TannerLiftedProduct
