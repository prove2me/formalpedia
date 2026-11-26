-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_fun_split_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:21.92209+00:00
-- url     : https://prove2.me/submissions/64760f49-9ee3-477c-a78e-946723a953da

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution {A M : Type*} [Fintype A] [AddCommMonoid M]
    (w : V) (F : (V → A) → M) :
    (∑ x : V → A, F x) =
      ∑ a : A, ∑ y : ({v : V // v ≠ w} → A),
        F ((Equiv.funSplitAt w A).symm (a, y)) := by
  calc
    (∑ x : V → A, F x) =
        ∑ p : A × ({v : V // v ≠ w} → A),
          F ((Equiv.funSplitAt w A).symm p) := by
            apply Fintype.sum_equiv (Equiv.funSplitAt w A)
            intro x
            exact congrArg F ((Equiv.funSplitAt w A).symm_apply_apply x).symm
    _ = _ := Fintype.sum_prod_type _
end Sabidussi.OddBalance
