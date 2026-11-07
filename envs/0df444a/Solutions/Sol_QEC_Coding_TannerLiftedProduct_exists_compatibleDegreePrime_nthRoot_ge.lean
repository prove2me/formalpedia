-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_compatibleDegreePrime_nthRoot_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:43.663349+00:00
-- url     : https://prove2.me/submissions/e39323ff-ad99-41ef-90ee-b8d03e93f347

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_CompatibleDegreePrime_degree_eq_block_mul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A target : Nat) (hA : 0 < A) (hOdd : Odd A) :
    ∃ a : CompatibleDegreePrime A,
      target ≤ Nat.nthRoot 6 a.blocks := by
  obtain ⟨a, haLarge⟩ :=
    exists_compatibleDegreePrime_gt A (A * target ^ 6) hA hOdd
  refine ⟨a, (Nat.le_nthRoot_iff (by norm_num)).2 ?_⟩
  have hScaled : A * target ^ 6 < A * a.blocks := by
    calc
      A * target ^ 6 < a.p := haLarge
      _ < a.p + 1 := by omega
      _ = A * a.blocks := a.degree_eq_block_mul
  exact (Nat.mul_lt_mul_left hA).mp hScaled |>.le
end QEC.Coding.TannerLiftedProduct
