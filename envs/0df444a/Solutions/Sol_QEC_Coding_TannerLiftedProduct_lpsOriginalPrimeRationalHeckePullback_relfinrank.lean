-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRationalHeckePullback_relfinrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:13:03.764071+00:00
-- url     : https://prove2.me/submissions/7aff640d-28be-40bb-befd-04257e565ac8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_fieldRange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (((lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield.subtype.comp
      (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N)).fieldRange).relfinrank
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalHeckePullback_fieldRange]
  exact lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN
end QEC.Coding.TannerLiftedProduct
