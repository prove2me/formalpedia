-- Prove2me | solution 1 for Sabidussi.OddBalance.cast_solutions_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:39.639111+00:00
-- url     : https://prove2.me/submissions/1e75dfe3-2d7e-4da3-8f3f-ee7f28c38183

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_F2_indicator_zero

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution (b : V → V → Fin 3 → Fin 3 → F2) :
    ((solutions b).card : F2) =
      ∑ x : V → Fin 3, ∏ v : V, (1 + obstruction b x v) := by
  rw [solutions]
  calc
    ((Finset.univ.filter fun x : V → Fin 3 =>
        ∀ v, obstruction b x v = 0).card : F2) =
        ∑ x : V → Fin 3, if ∀ v, obstruction b x v = 0 then 1 else 0 := by
          simpa using (Finset.sum_boole
            (R := F2) (fun x : V → Fin 3 => ∀ v, obstruction b x v = 0) Finset.univ).symm
    _ = ∑ x : V → Fin 3, ∏ v : V, (1 + obstruction b x v) := by
      apply Fintype.sum_congr
      intro x
      rw [show (if ∀ v, obstruction b x v = 0 then 1 else 0 : F2) =
          ∏ v : V, if obstruction b x v = 0 then 1 else 0 by
            simpa only [Finset.mem_univ, forall_const]
              using (Finset.prod_boole
                (s := Finset.univ) (p := fun v : V => obstruction b x v = 0)).symm]
      congr 1
      funext v
      exact F2.indicator_zero _
end Sabidussi.OddBalance
