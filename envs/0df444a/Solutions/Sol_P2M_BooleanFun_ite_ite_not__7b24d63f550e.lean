-- Prove2me | solution 1 for P2M_BooleanFun_ite_ite_not__7b24d63f550e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:34.681497+00:00
-- url     : https://prove2.me/submissions/a3a04ced-7d58-4109-8e71-1a3fefcc1834

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary

set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
variable {α : Sort*} {P : Prop} [Decidable P] {a b c : α}
namespace BooleanFun
theorem _root_.solution(P : Prop) [Decidable P] (a b c : α):
    ite (¬P) (ite P a b) c = ite (¬P) b c := by split_ifs <;> rfl
end BooleanFun
