-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGeneratedFieldPoint_secondHecke
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:02:33.759178+00:00
-- url     : https://prove2.me/submissions/c4ab19e2-3289-4ceb-8761-6760454a4b14

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalFrickeLevelPullback_eq_hecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerNormalGeneratedFieldPoint (N*p) (Nat.mul_pos hN hp) ≫
      lpsOriginalIntegerNormalGluedSecondLevelMap N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN hp) =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalHeckePullback N p hN hp h4N)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel,
    lpsOriginalRationalFrickeLevelPullback_eq_hecke]
end QEC.Coding.TannerLiftedProduct
