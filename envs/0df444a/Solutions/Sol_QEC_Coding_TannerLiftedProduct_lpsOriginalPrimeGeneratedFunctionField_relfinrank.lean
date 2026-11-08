-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGeneratedFunctionField_relfinrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:10:51.788719+00:00
-- url     : https://prove2.me/submissions/d5598117-af7f-434f-9005-b347c70cf506

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_relfinrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_index


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (hposN : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField (N*p)
        (Nat.mul_pos hposN (Fact.out : p.Prime).pos)) = p+1 := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [lpsOriginalGeneratedFunctionField_relfinrank_eq N (N*p)
    (dvd_mul_right N p) hN hposN (Nat.mul_pos hposN (Fact.out : p.Prime).pos)]
  exact lpsHeckeIntersection_index N p hNp
end QEC.Coding.TannerLiftedProduct
