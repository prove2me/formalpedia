-- Prove2me | solution 1 for Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_twoCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:09.693263+00:00
-- url     : https://prove2.me/submissions/75d10133-03a1-41a4-aea8-91017c81275b

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_F2_mul_self
import Theorems.Thm_Sabidussi_OddBalance_sum_fun_split_at
import Theorems.Thm_Sabidussi_OddBalance_Fintype_prod_eq_mul_mul_prod_compl_pair

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
    (S : Finset V) (f : Choice S) (v₀ v₁ : {v // v ∈ S})
    (hne : v₀ ≠ v₁)
    (hf₀ : (f v₀ : V) = v₁) (hf₁ : (f v₁ : V) = v₀)
    (hu₀ : ∀ v, (f v : V) = v₀ → v = v₁)
    (hu₁ : ∀ v, (f v : V) = v₁ → v = v₀) :
    totalChoiceTerm b S f = 0 := by
  have hvne : (v₀ : V) ≠ v₁ := by
    intro h
    exact hne (Subtype.ext h)
  rw [totalChoiceTerm, sum_fun_split_at (v₁ : V)]
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro y
  let x₀ : V → Fin 3 := (Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (0, y)
  let C : F2 := ∏ v ∈ ({v₀, v₁} : Finset {v // v ∈ S})ᶜ,
    b v (f v) (x₀ v) (x₀ (f v))
  have hfactor (a : Fin 3) :
      choiceTerm b S f ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y)) =
        b v₀ v₁ (y ⟨v₀, hvne⟩) a * C := by
    rw [choiceTerm, Fintype.prod_eq_mul_mul_prod_compl_pair v₀ v₁ hne]
    have hfac₀ :
        b v₀ (f v₀)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) v₀)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) (f v₀)) =
          b v₀ v₁ (y ⟨v₀, hvne⟩) a := by
      simp [Equiv.funSplitAt_symm_apply, hf₀, hvne]
    have hfac₁ :
        b v₁ (f v₁)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) v₁)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) (f v₁)) =
          b v₀ v₁ (y ⟨v₀, hvne⟩) a := by
      rw [hsymm]
      simp [Equiv.funSplitAt_symm_apply, hf₁, hvne]
    rw [hfac₀, hfac₁, F2.mul_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    have hvpair : v ≠ v₀ ∧ v ≠ v₁ := by simpa using hv
    have hv₀ : v ≠ v₀ := hvpair.1
    have hv₁ : v ≠ v₁ := hvpair.2
    have hvw : (v : V) ≠ v₁ := by
      intro h
      exact hv₁ (Subtype.ext h)
    have hfw : (f v : V) ≠ v₁ := by
      intro h
      exact hv₀ (hu₁ v h)
    simp [x₀, Equiv.funSplitAt_symm_apply, hvw, hfw]
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  rw [hrow, zero_mul]
end Sabidussi.OddBalance
