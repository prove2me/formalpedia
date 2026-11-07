-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:12.458373+00:00
-- url     : https://prove2.me/submissions/d67bf38d-535a-4659-8780-94b9a35be2f6

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
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
theorem _root_.solution [CommRing R] (n k : ℕ) (q : R) :
    qBinom (n + 1) (k + 1) q
      = qBinom n (k + 1) q + q ^ (n - k) * qBinom n k q := rfl
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
