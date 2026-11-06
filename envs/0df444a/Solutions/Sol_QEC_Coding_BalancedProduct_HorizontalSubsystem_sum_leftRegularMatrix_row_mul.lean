-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.HorizontalSubsystem.sum_leftRegularMatrix_row_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:28.63988+00:00
-- url     : https://prove2.me/submissions/edcf5bb4-c644-4de8-9c35-e5897e624113

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_sum_leftRegularMatrix_row

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.HorizontalSubsystem
theorem _root_.solution
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (go : G) (c : ZMod 2) :
    (∑ gi : G, LiftedProduct.leftRegularMatrix a go gi * c) =
      augmentation a * c := by
  rw [← Finset.sum_mul, sum_leftRegularMatrix_row]
end QEC.Coding.BalancedProduct.HorizontalSubsystem
