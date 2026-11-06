-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.GVPlus.localMatrix_primal_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:47:02.168738+00:00
-- url     : https://prove2.me/submissions/4a012c15-5083-4ccb-8735-23cc5043082a

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
    (m : Fin 202 → ZMod 2) (hm : m ≠ 0) :
    41 ≤ HammingWeight (systematicEncode localMatrix m) := by
  by_contra hweight
  have hbad : PrimalBad localMatrix := ⟨m, hm, by omega⟩
  exact localMatrix_good (Or.inl hbad)
end QEC.Coding.BalancedProduct.GVPlus
