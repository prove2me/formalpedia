-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:24:27.391897+00:00
-- url     : https://prove2.me/submissions/e6d30755-588b-4dbf-9018-f4c084fc2799

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner

set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype
namespace QEC.Coding.BalancedProduct.LPSTanner
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
    (y : Word (ZMod 2) κ) (i : ι) :
    wordLinearMapTranspose P y i =
      ∑ k : κ, y k * P (canonicalBasisWord i) k := by
  classical
  rw [wordLinearMapTranspose]
  rfl
end QEC.Coding.BalancedProduct.LPSTanner
