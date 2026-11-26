-- Prove2me | solution 1 for Sabidussi.OddBalance.exists_balanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:18:01.75439+00:00
-- url     : https://prove2.me/submissions/a0e6e296-f041-4310-b491-c4435188238e

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_solutions_card_odd

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
    ∃ x : V → Fin 3, ∀ v, obstruction b x v = 0 := by
  have hpos : 0 < (solutions b).card := (solutions_card_odd b hsymm hrow).pos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  refine ⟨x, ?_⟩
  simpa [solutions] using hx
end Sabidussi.OddBalance
