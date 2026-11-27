-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:08.117985+00:00
-- url     : https://prove2.me/submissions/5761729e-7391-474d-8fab-baf9ad7aed68

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_tau4_le_card
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    tau4 G = 0 ↔ ¬ HasC4 G := by
  constructor
  · intro h0 ⟨f, hf⟩
    obtain ⟨S, hS, hcard⟩ := exists_transversal_card_eq_tau4 G
    rw [h0, Finset.card_eq_zero] at hcard
    subst hcard
    obtain ⟨i, hi⟩ := hS f hf
    simp at hi
  · intro h
    have : c4Transversal G ∅ := fun f hf => (h ⟨f, hf⟩).elim
    exact Nat.le_zero.mp (tau4_le_card this)
end SizeRamsey.Plan
