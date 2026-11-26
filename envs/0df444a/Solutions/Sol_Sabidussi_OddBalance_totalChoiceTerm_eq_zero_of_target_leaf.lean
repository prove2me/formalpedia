-- Prove2me | solution 1 for Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_target_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:55.546437+00:00
-- url     : https://prove2.me/submissions/45b24d1c-bdcb-4b4b-8b43-356caf804303

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_sum_fun_split_at

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ : {v // v ∈ S}) (w : V)
    (hw : (f v₀ : V) = w) (hnotSource : ∀ v, (v : V) ≠ w)
    (huniqueTarget : ∀ v, (f v : V) = w → v = v₀) :
    totalChoiceTerm b S f = 0 := by
  rw [totalChoiceTerm, sum_fun_split_at w]
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro y
  let x₀ : V → Fin 3 := (Equiv.funSplitAt w (Fin 3)).symm (0, y)
  let C : F2 := ∏ v ∈ ({v₀} : Finset {v // v ∈ S})ᶜ,
    b v (f v) (x₀ v) (x₀ (f v))
  have hfactor (a : Fin 3) :
      choiceTerm b S f ((Equiv.funSplitAt w (Fin 3)).symm (a, y)) =
        b v₀ w (y ⟨v₀, hnotSource v₀⟩) a * C := by
    rw [choiceTerm, Fintype.prod_eq_mul_prod_compl v₀]
    congr 1
    · simp [Equiv.funSplitAt_symm_apply, hw, hnotSource]
    · apply Finset.prod_congr rfl
      intro v hv
      have hvne : v ≠ v₀ := by simpa using hv
      have hfw : (f v : V) ≠ w := by
        intro h
        exact hvne (huniqueTarget v h)
      simp [x₀, Equiv.funSplitAt_symm_apply, hnotSource, hfw]
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  rw [hrow, zero_mul]
end Sabidussi.OddBalance
