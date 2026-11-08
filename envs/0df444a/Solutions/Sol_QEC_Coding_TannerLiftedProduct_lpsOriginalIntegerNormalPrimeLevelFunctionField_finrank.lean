-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalPrimeLevelFunctionField_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:17:54.319205+00:00
-- url     : https://prove2.me/submissions/dcf101a8-dc42-459e-9a7e-6cf29b916bcc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLevelFunctionField_finrank
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)
    letI := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).functionField = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
  rw [lpsOriginalIntegerNormalLevelFunctionField_finrank N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)]
  exact lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN
end QEC.Coding.TannerLiftedProduct
