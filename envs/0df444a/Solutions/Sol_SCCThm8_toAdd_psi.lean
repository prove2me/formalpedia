-- Prove2me | solution 1 for SCCThm8.toAdd_psi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:01.476426+00:00
-- url     : https://prove2.me/submissions/012b2b10-968f-4945-9abc-22c65ea00f72

module
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} (u : Fin n → Multiplicative ℤ) (e : Fin n → ℤ) :
    Multiplicative.toAdd (psi u e) = ∑ i, e i * Multiplicative.toAdd (u i) := by
  unfold psi
  rw [Fin.sum_univ_def]
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.map_cons, List.prod_cons, toAdd_mul, ih, toAdd_zpow]
end SCCThm8
