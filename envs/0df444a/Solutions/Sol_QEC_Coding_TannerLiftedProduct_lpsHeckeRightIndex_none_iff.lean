-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:56.727837+00:00
-- url     : https://prove2.me/submissions/085bedaa-7f96-4b26-8206-7eedb5ea99a4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_conjugateMatrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_of_conjugate
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
    lpsHeckeRightIndex N p hNp γ hγ none=none ↔ γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by
  constructor
  · intro hi
    obtain ⟨δ,hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ none
    rw [hi] at he
    exact lpsHeckeIntersection_of_conjugate N p γ δ hδ
      (lpsHeckeRightFactorGL ℝ p none none γ δ he)
  · intro hγ'
    obtain ⟨δ,_hδ,he⟩ := lpsHeckeIntersection_conjugateMatrix N p γ hγ'
    exact lpsHeckeRightIndex_of_factor N p hNp γ hγ none none δ he
end QEC.Coding.TannerLiftedProduct
