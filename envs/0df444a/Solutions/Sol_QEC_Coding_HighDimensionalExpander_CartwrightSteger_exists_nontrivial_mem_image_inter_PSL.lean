-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_nontrivial_mem_image_inter_PSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:16.376802+00:00
-- url     : https://prove2.me/submissions/7b3864ca-8b38-4eba-a6be-dd63117cc2dc

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerClassGenerator_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_lt_natCard_constantProjectiveClass
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ker_residueProjectiveDetClass_eq_PSL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ g : PGL P r level,
      g ∈ IndexCartwrightStegerImage P r level ∧
      g ∈ PSL P r level ∧ g ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (ConstantProjectiveClass P r)
  let gu := indexCartwrightStegerClassGenerator P r level u
  let gv := indexCartwrightStegerClassGenerator P r level v
  refine ⟨gu * gv⁻¹,
    (IndexCartwrightStegerImage P r level).mul_mem
      (indexCartwrightStegerGenerator_mem_image P r level u)
      ((IndexCartwrightStegerImage P r level).inv_mem
        (indexCartwrightStegerGenerator_mem_image P r level v)), ?_, ?_⟩
  · rw [← ker_residueProjectiveDetClass_eq_PSL P r level,
      MonoidHom.mem_ker, map_mul, map_inv]
    rw [residueProjectiveDetClass_indexCartwrightStegerClassGenerator,
      residueProjectiveDetClass_indexCartwrightStegerClassGenerator,
      mul_inv_cancel]
  · intro hone
    have heq : gu = gv := by
      apply (mul_inv_eq_one.mp hone)
    exact huv ((indexCartwrightStegerClassGenerator_injective P r level) heq)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
