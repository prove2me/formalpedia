-- Prove2me | solution 1 for SymBoolPCSP.Galois.sandwich
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:11:06.793578+00:00
-- url     : https://prove2.me/submissions/d0151338-005b-4288-8ee9-d9b6d95474e0

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic
set_option autoImplicit false
open SymBoolPCSP.Galois PCSPBLPAff.Symmetric

theorem solution {D : Type} [Fintype D] [DecidableEq D] {k : ℕ}
    (P Q P' Q' : Set (Fin k → D)) (hP' : P' ⊆ P) (hPQ : P ⊆ Q) (hQ' : Q ⊆ Q') :
    PPPDefinable (single P) (single Q) P' Q' := by
  refine ⟨0, ⟨k, 1, fun _ => Sum.inl (), fun _ i => i⟩, by simp, ?_, ?_⟩
  · intro x hx
    refine ⟨Fin.elim0, ?_⟩
    intro j
    simp only [Function.comp_def, withEqual, single]
    have e : ((fun v => Fin.append x (Fin.elim0 : Fin 0 → D) (Fin.cast (show k = k + 0 from rfl) v)) ∘ fun i : Fin k => i) = x := by
      funext i
      exact Fin.append_left x (Fin.elim0 : Fin 0 → D) i
    show ((fun v => Fin.append x (Fin.elim0 : Fin 0 → D) (Fin.cast (show k = k + 0 from rfl) v)) ∘ fun i : Fin k => i) ∈ P
    rw [e]
    exact hP' hx
  · intro z hz
    have := hz 0
    simp only [Function.comp_def, withEqual, single] at this
    exact hQ' this
