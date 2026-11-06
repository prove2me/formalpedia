-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.GVPlus.localMatrix_dual_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:47:12.524524+00:00
-- url     : https://prove2.me/submissions/411a2bf8-cb03-48d9-b820-ec3b99a0e826

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.FieldTheory.Finiteness
import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localMatrix_good

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.BalancedProduct.GVPlus
open Classical
attribute [local instance] QEC.Coding.BalancedProduct.GVPlus.localMatrixFintype
namespace QEC.Coding.BalancedProduct.GVPlus
theorem _root_.solution
    (y : Fin 200 → ZMod 2) (hy : y ≠ 0) :
    41 ≤ HammingWeight (systematicDualEncode localMatrix y) := by
  by_contra hweight
  have hbad : DualBad localMatrix := ⟨y, hy, by omega⟩
  exact localMatrix_good (Or.inr hbad)
end QEC.Coding.BalancedProduct.GVPlus
