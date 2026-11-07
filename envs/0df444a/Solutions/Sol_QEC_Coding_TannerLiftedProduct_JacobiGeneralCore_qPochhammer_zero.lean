-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:21.698562+00:00
-- url     : https://prove2.me/submissions/61a48778-332c-4f30-9c26-6f371d25af35

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
theorem _root_.solution [CommRing R] (a q : R) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
