-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:02.882399+00:00
-- url     : https://prove2.me/submissions/ba09c6e6-d407-43ae-a84c-c179f7bb4ff3

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_eq_zero_of_lt

set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
theorem _root_.solution [CommRing R] (q : R) : ∀ n : ℕ, qBinom n n q = 1
  | 0 => rfl
  | n + 1 => by
    rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n),
        solution q n, Nat.sub_self, pow_zero]
    ring
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
