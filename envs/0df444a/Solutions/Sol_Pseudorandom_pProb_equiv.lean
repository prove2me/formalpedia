-- Prove2me | solution 1 for Pseudorandom.pProb_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:58.56573+00:00
-- url     : https://prove2.me/submissions/a58a8ff1-4034-4366-884d-24b08818821a

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_equiv

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]
namespace Pseudorandom
theorem _root_.solution (e : ι ≃ κ) (P : ι → α → ℝ) (S : (ι → α) → Prop) :
    pProb P S = pProb (fun j => P (e.symm j)) (fun ω' => S (ω' ∘ e)) := by
  classical
  unfold pProb
  rw [pE_equiv e]
end Pseudorandom
