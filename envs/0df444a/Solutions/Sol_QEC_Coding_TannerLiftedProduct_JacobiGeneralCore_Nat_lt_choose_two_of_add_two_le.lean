-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:33.216198+00:00
-- url     : https://prove2.me/submissions/65cd43e3-8723-4655-abf9-a4590eb859e7

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_le_choose_two_add_one

set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
theorem _root_.solution {d k : ℕ} (hk : d + 2 ≤ k) : d < k.choose 2 := by
  have := le_choose_two_add_one k
  omega
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
