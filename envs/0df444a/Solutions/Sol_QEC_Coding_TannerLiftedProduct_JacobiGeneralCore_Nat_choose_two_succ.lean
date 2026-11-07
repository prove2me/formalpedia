-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.choose_two_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:11.586808+00:00
-- url     : https://prove2.me/submissions/e3653c0d-1473-49b1-a12f-c0b99d1df151

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs

set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
theorem _root_.solution (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
