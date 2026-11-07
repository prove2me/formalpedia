-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two__59bcef2a28c6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:01.993202+00:00
-- url     : https://prove2.me/submissions/55b121f2-b0c4-4396-8c05-7e8049c94cab

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two

set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
theorem _root_.solution (n l : ℕ) :
    n.choose 2 + (n + (l + 1)).choose 2 + (n + (l + 1)) =
    (l + 2).choose 2 + n * (n + (l + 1)) := by
  have h := choose_two_add_choose_two n (l + 1)
  have h2 : (l + 2).choose 2 = (l + 1).choose 2 + (l + 1) := choose_two_succ (l + 1)
  linarith
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
