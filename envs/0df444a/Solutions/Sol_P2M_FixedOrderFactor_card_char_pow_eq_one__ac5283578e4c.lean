-- Prove2me | solution 1 for P2M_FixedOrderFactor_card_char_pow_eq_one__ac5283578e4c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:17.898643+00:00
-- url     : https://prove2.me/submissions/a312f64b-86fd-4170-9b7a-57d926dbc419

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
public import Theorems.Thm_FixedOrderFactor_mem_dualPowers_iff
public import Theorems.Thm_FixedOrderFactor_card_dualPowers

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
open Classical
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : r ∣ p - 1) :
    ((Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1)).card = r := by
  trans Fintype.card (dualPowers p r)
  · rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun χ => by
    rw [Finset.mem_filter, mem_dualPowers_iff]; simp))
  · rw [← Nat.card_eq_fintype_card, card_dualPowers p hr]
end FixedOrderFactor
