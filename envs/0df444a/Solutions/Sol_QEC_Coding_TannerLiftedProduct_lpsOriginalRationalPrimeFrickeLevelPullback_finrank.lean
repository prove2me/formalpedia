-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalPrimeFrickeLevelPullback_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:05:36.223378+00:00
-- url     : https://prove2.me/submissions/5e2841fd-0c9f-4e79-a555-d1fc986a665a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalFrickeLevelPullback_finrank
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      (lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    letI : Module (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := Algebra.toModule
    Module.finrank (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
  rw [lpsOriginalRationalFrickeLevelPullback_finrank]
  exact lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN
end QEC.Coding.TannerLiftedProduct
