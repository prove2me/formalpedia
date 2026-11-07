-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:52:22.814515+00:00
-- url     : https://prove2.me/submissions/424f424c-034a-4976-8ed9-6a86e83996c0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank


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
    ((lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalDilationFractionPullback p (Fact.out : p.Prime).pos).toRingHom).relfinrank
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalGeneratedFunctionFieldQ_dilation_image_eq_fricke]
  have h := Subfield.relfinrank_map_map
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield
    (lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield
    (lpsOriginalPositiveFractionPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))).toRingHom
  rw [lpsOriginalGeneratedFunctionFieldQ_fricke_map] at h
  exact h.trans (lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN)
end QEC.Coding.TannerLiftedProduct
