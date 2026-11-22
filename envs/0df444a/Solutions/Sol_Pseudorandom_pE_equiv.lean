-- Prove2me | solution 1 for Pseudorandom.pE_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:03.043507+00:00
-- url     : https://prove2.me/submissions/a44c42fb-0960-4bcc-89ca-633a5006e87b

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]
namespace Pseudorandom
theorem _root_.solution (e : ι ≃ κ) (P : ι → α → ℝ) (f : (ι → α) → ℝ) :
    pE P f = pE (fun j => P (e.symm j)) (fun ω' => f (ω' ∘ e)) := by
  unfold pE pw
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl α)) _ _ fun ω => ?_
  have h1 : (Equiv.arrowCongr e (Equiv.refl α) ω) ∘ e = ω := by
    funext i; simp [Equiv.arrowCongr_apply]
  dsimp only
  rw [h1]
  congr 1
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Equiv.arrowCongr_apply]
end Pseudorandom
