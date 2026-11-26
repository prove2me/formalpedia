-- Prove2me | solution 1 for Sabidussi.orderedPairBracket_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:25.511841+00:00
-- url     : https://prove2.me/submissions/728bd9ac-d1ad-4aa8-86d2-1313b6e6b62e

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_add_left
import Theorems.Thm_Sabidussi_bracket_comm
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero


section
namespace Sabidussi
open scoped BigOperators
private theorem orderedPairBracket_inner_castSucc {n : ℕ} (f : Fin (n + 1) → Color)
    (i : Fin n) :
    (∑ j : Fin (n + 1),
        if j < i.castSucc then bracket (f i.castSucc) (f j) else 0) =
      ∑ j : Fin n, if j < i then bracket (f i.castSucc) (f j.castSucc) else 0 := by
  rw [Fin.sum_univ_castSucc]
  have hnlt : ¬ Fin.last n < i.castSucc := (Fin.castSucc_lt_last i).asymm
  rw [if_neg hnlt, add_zero]
  simp
private theorem orderedPairBracket_inner_last {n : ℕ} (f : Fin (n + 1) → Color) :
    (∑ j : Fin (n + 1),
        if j < Fin.last n then bracket (f (Fin.last n)) (f j) else 0) =
      ∑ j : Fin n, bracket (f j.castSucc) (f (Fin.last n)) := by
  calc
    _ = ∑ j : Fin n, bracket (f (Fin.last n)) (f j.castSucc) := by
      rw [Fin.sum_univ_castSucc]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact bracket_comm _ _
end Sabidussi
end

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution {n : ℕ} (f : Fin (n + 1) → Color) :
    orderedPairBracket f =
      orderedPairBracket (fun i : Fin n ↦ f i.castSucc) +
        bracket (∑ i : Fin n, f i.castSucc) (f (Fin.last n)) := by
  unfold orderedPairBracket
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact orderedPairBracket_inner_castSucc f i
  · rw [orderedPairBracket_inner_last]
    let g : Color →+ F₂ :=
      { toFun := fun x ↦ bracket x (f (Fin.last n))
        map_zero' := bracket_zero_left _
        map_add' := fun x y ↦ bracket_add_left x y _ }
    change (∑ i : Fin n, g (f i.castSucc)) = g (∑ i : Fin n, f i.castSucc)
    exact (map_sum g (fun i : Fin n ↦ f i.castSucc) Finset.univ).symm
end Sabidussi
