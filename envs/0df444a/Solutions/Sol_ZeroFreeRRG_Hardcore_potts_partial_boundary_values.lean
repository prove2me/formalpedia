-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_partial_boundary_values
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:44:36.894749+00:00
-- url     : https://prove2.me/submissions/159b1f82-9295-45d2-8b4b-1d5beafaa77a

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (τ : V → Fin q) :
    pottsPartialZ q G β ∅ τ = pottsZ q G β ∧
    pottsPartialZ q G β Finset.univ τ = β ^ monoEdges G τ := by
  classical
  constructor
  · simp [pottsPartialZ,pottsZ]
  · unfold pottsPartialZ
    have heq (σ : V → Fin q) : (∀ v ∈ (Finset.univ : Finset V), σ v=τ v) ↔ σ=τ := by
      simp only [Finset.mem_univ,forall_true_left,funext_iff]
    simp only [heq]
    simp
