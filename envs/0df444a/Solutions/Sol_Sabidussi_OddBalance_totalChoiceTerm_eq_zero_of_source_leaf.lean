-- Prove2me | solution 1 for Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_source_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:47.600834+00:00
-- url     : https://prove2.me/submissions/c190ba9f-7f30-4d0e-81ad-77115ecac15e

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
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ : {v // v ∈ S}) (w : V)
    (hw : (v₀ : V) = w) (hnotTarget : ∀ v, (f v : V) ≠ w) :
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
        b w (f v₀) a (y ⟨f v₀, hnotTarget v₀⟩) * C := by
    rw [choiceTerm, Fintype.prod_eq_mul_prod_compl v₀]
    congr 1
    · simp [Equiv.funSplitAt_symm_apply, hw, hnotTarget]
    · apply Finset.prod_congr rfl
      intro v hv
      have hvne : v ≠ v₀ := by simpa using hv
      have hvw : (v : V) ≠ w := by
        intro h
        apply hvne
        apply Subtype.ext
        simpa [hw] using h
      simp [C, x₀, Equiv.funSplitAt_symm_apply, hvw, hnotTarget]
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  suffices (∑ a : Fin 3, b w (f v₀) a (y ⟨f v₀, hnotTarget v₀⟩)) = 0 by
    rw [this, zero_mul]
  calc
    (∑ a : Fin 3, b w (f v₀) a (y ⟨f v₀, hnotTarget v₀⟩)) =
        ∑ a : Fin 3, b (f v₀) w (y ⟨f v₀, hnotTarget v₀⟩) a := by
          apply Fintype.sum_congr
          intro a
          exact hsymm _ _ _ _
    _ = 0 := hrow (f v₀) w (y ⟨f v₀, hnotTarget v₀⟩)
end Sabidussi.OddBalance
