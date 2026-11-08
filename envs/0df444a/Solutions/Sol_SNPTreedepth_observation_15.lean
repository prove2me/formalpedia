-- Prove2me | solution 1 for SNPTreedepth.observation_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:42:53.960325+00:00
-- url     : https://prove2.me/submissions/285354ae-2c8f-4c1f-bf19-dc69411ddb85

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_Sentence

set_option autoImplicit false

open SNPTreedepth in
theorem solution {σ : SNPTreedepth.Signature} {V : Type*} [Fintype V] [Nonempty V]
    (φ : SNPTreedepth.Sentence σ)
    (hφ : φ.WellFormed) (R : SNPTreedepth.Structure σ V) (hR : φ.Models R) (U : Set V)
    (hU : U.Nonempty) :
    φ.Models (R.induce U) := by
  obtain ⟨S, hS⟩ := hR
  refine ⟨fun j => {u | (fun t => (u t : V)) ∈ S j}, fun x => ?_⟩
  have hx := hS (fun t => (x t : V))
  unfold SNPTreedepth.Sentence.Holds at hx ⊢
  have hval : ∀ a, φ.atomHolds (R.induce U) (fun j => {u | (fun t => (u t : V)) ∈ S j}) x a ↔
      φ.atomHolds R S (fun t => (x t : V)) a := by
    intro a
    cases a with
    | inp i args => exact Iff.rfl
    | var j args => exact Iff.rfl
    | eq n n' => exact Subtype.ext_iff
  have key : ∀ ψ : SNPTreedepth.NNF (SNPTreedepth.Atom σ φ.r φ.arR φ.k),
      ψ.eval (φ.atomHolds (R.induce U) (fun j => {u | (fun t => (u t : V)) ∈ S j}) x) ↔
      ψ.eval (φ.atomHolds R S (fun t => (x t : V))) := by
    intro ψ
    induction ψ with
    | pos a => exact hval a
    | neg a => exact not_congr (hval a)
    | and p q ihp ihq => exact and_congr ihp ihq
    | or p q ihp ihq => exact or_congr ihp ihq
  exact (key φ.ψ).2 hx
