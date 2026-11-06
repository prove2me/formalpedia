-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.GVPlus.exists_binary_localCode_402_202_distance41
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:53:33.840278+00:00
-- url     : https://prove2.me/submissions/8c00308c-6124-4e54-8fa7-6370aaa48d30

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.FieldTheory.Finiteness
import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_length
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_dimension
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_dimension_gt_half_length
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_primal_weight_lower_bound
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_dual_weight_lower_bound

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.BalancedProduct.GVPlus
open Classical
attribute [local instance] QEC.Coding.BalancedProduct.GVPlus.localMatrixFintype
namespace QEC.Coding.BalancedProduct.GVPlus
theorem _root_.solution :
    ∃ C : LinearCode (ZMod 2) LocalCoordinate,
      Length (ZMod 2) LocalCoordinate = 402 ∧
      Dimension C = 202 ∧
      402 / 2 < Dimension C ∧
      (∀ x : Word (ZMod 2) LocalCoordinate,
        x ∈ C.carrier → x ≠ 0 → 41 ≤ HammingWeight x) ∧
      (∀ x : Word (ZMod 2) LocalCoordinate,
        x ∈ C.dual.carrier → x ≠ 0 → 41 ≤ HammingWeight x) := by
  exact ⟨localCode, localCode_length, localCode_dimension,
    localCode_dimension_gt_half_length,
    localCode_primal_weight_lower_bound, localCode_dual_weight_lower_bound⟩
end QEC.Coding.BalancedProduct.GVPlus
