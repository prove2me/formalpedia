-- Prove2me | solution 1 for SoficGroups.elementaryUnit_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/bbf19fc0-5dea-4512-bf82-22c63a25b466

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
namespace SoficGroups
theorem _root_.solution (i j : ι) (h : i ≠ j) :
    Function.Injective (elementaryUnit (R := R) i j h) := by
  intro a b hab
  have he := congrArg (fun z : (Matrix ι ι R)ˣ => (z : Matrix ι ι R) i j) hab
  simpa [elementaryUnit, Matrix.one_apply, h] using he
end SoficGroups
