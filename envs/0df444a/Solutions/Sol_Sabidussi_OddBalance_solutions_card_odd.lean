-- Prove2me | solution 1 for Sabidussi.OddBalance.solutions_card_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:26.899671+00:00
-- url     : https://prove2.me/submissions/b7ec8222-d149-4b07-8f7e-3bd607cea18a

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_cast_solutions_card_eq_one

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0) :
    Odd (solutions b).card :=
  ZMod.natCast_eq_one_iff_odd.mp (cast_solutions_card_eq_one b hsymm hrow)
end Sabidussi.OddBalance
