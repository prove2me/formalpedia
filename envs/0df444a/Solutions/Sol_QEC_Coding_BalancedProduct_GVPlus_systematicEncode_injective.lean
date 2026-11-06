-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.GVPlus.systematicEncode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:46:29.524445+00:00
-- url     : https://prove2.me/submissions/b2e76914-0951-47b0-9605-ec3ebdfd6722

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.FieldTheory.Finiteness
import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.BalancedProduct.GVPlus
open Classical
namespace QEC.Coding.BalancedProduct.GVPlus
theorem _root_.solution {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) :
    Function.Injective (systematicEncode A) := by
  intro x y hxy
  funext i
  exact congrFun hxy (Sum.inl i)
end QEC.Coding.BalancedProduct.GVPlus
