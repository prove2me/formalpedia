-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:50.682953+00:00
-- url     : https://prove2.me/submissions/3e65c836-2877-4235-acb8-95be897e0c4c

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_succ

set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
theorem _root_.solution [CommRing R] (q : R) :
    ∀ {n k : ℕ}, n < k → qBinom n k q = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl _)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [qBinom_succ_succ,
        solution q (show n < k + 1 by omega),
        solution q (show n < k by omega)]
    ring
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
