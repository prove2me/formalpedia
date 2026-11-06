-- Prove2me | solution 2 for QEC.Coding.BalancedProduct.GVPlus.systematicDualEncode_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:00:13.603648+00:00
-- url     : https://prove2.me/submissions/02f79da9-0308-42c5-b0e8-ba9cca899a08

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
