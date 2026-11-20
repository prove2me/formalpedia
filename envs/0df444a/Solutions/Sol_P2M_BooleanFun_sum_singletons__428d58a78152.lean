-- Prove2me | solution 1 for P2M_BooleanFun_sum_singletons__428d58a78152
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:29.862809+00:00
-- url     : https://prove2.me/submissions/7e53652c-da35-4f92-9c93-83ed6a4423e8

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary
import Theorems.Thm_BooleanFun_sum_singletons

set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
namespace BooleanFun
theorem _root_.solution [AddCommMonoid α] {F : Finset ι → α}:
    ∑ S ∈ {S|S.card = 1}, F S = ∑ i, F {i} := by apply sum_singletons; intro i; rfl
end BooleanFun
