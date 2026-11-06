-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.GVPlus.systematicDualEncode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:53:16.159657+00:00
-- url     : https://prove2.me/submissions/25a813c5-b693-4b2e-953b-f51d4164e175

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
    Function.Injective (systematicDualEncode A) := by
  intro x y hxy
  funext j
  exact congrFun hxy (Sum.inr j)
end QEC.Coding.BalancedProduct.GVPlus
