-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:01:52.242377+00:00
-- url     : https://prove2.me/submissions/070ae886-5a22-4689-9d5a-c8197e31af8f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_index


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (hposN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hposN (Fact.out : p.Prime).pos)) = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq N (N*p)
    (dvd_mul_right N p) hN hposN (Nat.mul_pos hposN (Fact.out : p.Prime).pos)]
  exact lpsHeckeIntersection_index N p hNp
end QEC.Coding.TannerLiftedProduct
