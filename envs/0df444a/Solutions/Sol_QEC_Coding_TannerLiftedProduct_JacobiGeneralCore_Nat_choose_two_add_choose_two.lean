-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.choose_two_add_choose_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:58.831205+00:00
-- url     : https://prove2.me/submissions/abd5e525-dbff-470a-8634-936a67da9685

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_succ

set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
theorem _root_.solution (m k : ℕ) :
    (m + k).choose 2 + m.choose 2 + m = k.choose 2 + m * (m + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 from by omega, choose_two_succ, choose_two_succ]; linarith
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
