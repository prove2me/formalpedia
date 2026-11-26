-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_one_fin3_assignments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:20.342325+00:00
-- url     : https://prove2.me/submissions/93b45cc8-50ad-4778-a4e8-6ffd39bbcb02

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
theorem _root_.solution : (∑ _x : V → Fin 3, (1 : F2)) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (3 : F2) = 1 by decide]
  simp
end Sabidussi.OddBalance
