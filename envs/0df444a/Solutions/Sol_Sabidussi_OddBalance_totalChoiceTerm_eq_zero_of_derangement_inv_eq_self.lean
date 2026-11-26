-- Prove2me | solution 1 for Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_derangement_inv_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:46.449562+00:00
-- url     : https://prove2.me/submissions/0aceb4a7-c1a5-4264-b8a0-619e084a2ee5

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_eq_zero_of_twoCycle

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
    (S : Finset V) (hS : S.Nonempty) (d : Derangement S) (hd : d.inv = d) :
    totalChoiceTerm b S d.choice = 0 := by
  let v₀ : {v // v ∈ S} := ⟨hS.choose, hS.choose_spec⟩
  let v₁ : {v // v ∈ S} := d.1 v₀
  have hne : v₀ ≠ v₁ := (d.2 v₀).symm
  have hsigma : d.1.symm = d.1 := congrArg Subtype.val hd
  have hcycle : d.1 v₁ = v₀ := by
    have h := d.1.symm_apply_apply v₀
    rw [hsigma] at h
    exact h
  apply totalChoiceTerm_eq_zero_of_twoCycle b hsymm hrow S d.choice v₀ v₁ hne
  · rfl
  · exact congrArg Subtype.val hcycle
  · intro v hv
    apply d.1.injective
    calc
      d.1 v = v₀ := Subtype.ext hv
      _ = d.1 v₁ := hcycle.symm
  · intro v hv
    apply d.1.injective
    calc
      d.1 v = v₁ := Subtype.ext hv
      _ = d.1 v₀ := rfl
end Sabidussi.OddBalance
