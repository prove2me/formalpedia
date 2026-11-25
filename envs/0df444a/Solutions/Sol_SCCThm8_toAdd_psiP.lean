-- Prove2me | solution 1 for SCCThm8.toAdd_psiP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:12.606038+00:00
-- url     : https://prove2.me/submissions/c95421d9-c821-4924-82c6-74079ea35b0b

module
public import Definitions.Def_SCCThm8_PowerRigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Theorems.Thm_SCCThm8_toAdd_psi


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {m n : ℕ} (u : Fin m → Fin n → Multiplicative ℤ) (e : Fin m → Fin n → ℤ) :
    Multiplicative.toAdd (psiP u e) = ∑ j, ∑ i, e j i * Multiplicative.toAdd (u j i) := by
  have : Multiplicative.toAdd (psiP u e) = ∑ j, Multiplicative.toAdd (psi (u j) (e j)) := by
    unfold psiP
    rw [Fin.sum_univ_def]
    generalize List.finRange m = l
    induction l with
    | nil => rfl
    | cons x l ih => simp [List.map_cons, List.prod_cons, toAdd_mul, ih]
  rw [this]
  exact sum_congr rfl fun j _ => toAdd_psi (u j) (e j)
end SCCThm8
