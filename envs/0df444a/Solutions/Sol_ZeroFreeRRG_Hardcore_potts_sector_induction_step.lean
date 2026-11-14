-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_sector_induction_step
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:03:39.32093+00:00
-- url     : https://prove2.me/submissions/fe662785-7422-4a0b-a48e-1a6cd496e276

import Theorems.Thm_ZeroFreeRRG_Hardcore_unit_chord_sum_nonzero
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_vertex_recursion
import Mathlib
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution {V : Type} [Fintype V] (q : ℕ) (hq : 1 ≤ q) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S) (u : ℂ) (hu : ‖u‖ = 1)
    (hn : ∀ c : Fin q, pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) ≠ 0)
    (hclose : ∀ c : Fin q, ‖u - (pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)) /
      (‖pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)‖ : ℂ)‖ ≤ 1/2) :
    pottsWeightedPartial q G W hW S τ ≠ 0 := by
  classical
  let z := fun c : Fin q => pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)
  have hset : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  have hh := unit_chord_sum_nonzero Finset.univ z u hu hset (fun i _ => hn i) (fun i _ => hclose i)
  rw [potts_weighted_vertex_recursion q G W hW S τ v hv]
  exact hh.2
