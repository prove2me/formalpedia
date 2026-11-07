-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.CompatibleDegreePrime.blocks_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:39.721962+00:00
-- url     : https://prove2.me/submissions/827b7a86-9bb8-46b9-b7ae-b5654833c878

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
namespace CompatibleDegreePrime
theorem _root_.solution
    {A : Nat} (a : CompatibleDegreePrime A) (hA : 0 < A) :
    0 < a.blocks := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (by omega) a.blockDvdDegree
  · exact hA
end CompatibleDegreePrime
end QEC.Coding.TannerLiftedProduct
