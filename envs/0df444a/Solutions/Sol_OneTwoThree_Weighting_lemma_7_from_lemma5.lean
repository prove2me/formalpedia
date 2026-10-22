-- Prove2me | solution 1 for OneTwoThree.Weighting.lemma_7_from_lemma5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:40:40.665248+00:00
-- url     : https://prove2.me/submissions/c75f0b25-efd8-4e1b-b92c-2dbc31fdf289

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

set_option autoImplicit false
open Finset SimpleGraph OneTwoThree.Weighting

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (R B : Finset V)
    (hRB : IsGoodPartition G Finset.univ R B)
    (hengine : ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ R, Even (wdeg G ω v)) ∧
      ∃ f : V → ℕ, (∀ v ∈ B, wdeg G ω v = f v) ∧
        (∀ v ∈ B, Odd (f v)) ∧
        (∀ u v, u ∈ B → v ∈ B → G.Adj u v → f u ≠ f v)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω ∧
      ∀ v, Even (wdeg G ω v) ↔ v ∈ R := by
  obtain ⟨hdisj, hunion, hind, -, -⟩ := hRB
  obtain ⟨ω, hω, hR, f, hB, hodd, hf⟩ := hengine
  have hcov : ∀ v, v ∈ R ∨ v ∈ B := by
    intro v
    have : v ∈ R ∪ B := by rw [hunion]; exact Finset.mem_univ v
    exact Finset.mem_union.mp this
  have hnotB : ∀ v, v ∈ R → v ∉ B := fun v hv hvB =>
    Finset.disjoint_left.mp hdisj hv hvB
  have hevenB : ∀ v ∈ B, ¬ Even (wdeg G ω v) := by
    intro v hv he
    rw [hB v hv] at he
    exact (Nat.not_even_iff_odd.mpr (hodd v hv)) he
  refine ⟨ω, hω, ?_, ?_⟩
  · intro v w hvw
    rcases hcov v with hv | hv <;> rcases hcov w with hw | hw
    · exact absurd hvw (hind hv hw hvw.ne)
    · intro h
      exact hevenB w hw (h ▸ hR v hv)
    · intro h
      exact hevenB v hv (h ▸ hR w hw)
    · rw [hB v hv, hB w hw]
      exact hf v w hv hw hvw
  · intro v
    rcases hcov v with hv | hv
    · exact ⟨fun _ => hv, fun _ => hR v hv⟩
    · exact ⟨fun h => absurd h (hevenB v hv), fun h => absurd hv (hnotB v h)⟩
