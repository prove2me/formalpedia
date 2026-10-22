-- Prove2me | solution 1 for P7ThreeColor.Seed.dominating_of_dominating
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:06:28.998261+00:00
-- url     : https://prove2.me/submissions/3e1c1b14-6416-4b0a-bc71-20d3cc32e38f

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

set_option autoImplicit false
open P7ThreeColor.Seed

theorem mem_cl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V) (v : V) :
    v ∈ P7ThreeColor.Seed.closure G T ↔ v ∈ T ∨ ∃ t ∈ T, G.Adj v t := by
  unfold P7ThreeColor.Seed.closure P7ThreeColor.Seed.nbhd
  classical
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hv : v ∈ T
      · exact Or.inl hv
      · exact Or.inr ⟨hv, h⟩

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hS : IsDominating G S) (hTS : T ⊆ S)
    (hTdom : ∀ v ∈ S, v ∈ T ∨ ∃ t ∈ T, G.Adj v t)
    (hTconn : (G.induce (T : Set V)).Connected) :
    (G.induce (T : Set V)).Connected ∧ IsTwoDominating G T := by
  refine ⟨hTconn, ?_⟩
  have hS' : ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj v s := by
    intro v
    have : v ∈ P7ThreeColor.Seed.closure G S := by
      have h : P7ThreeColor.Seed.closure G S = Finset.univ := hS
      rw [h]; exact Finset.mem_univ v
    exact (mem_cl G S v).1 this
  have key : ∀ v ∈ S, v ∈ P7ThreeColor.Seed.closure G T := fun v hv => (mem_cl G T v).2 (hTdom v hv)
  unfold IsTwoDominating IsDominating
  apply Finset.eq_univ_of_forall
  intro v
  rw [mem_cl]
  rcases hS' v with h | ⟨s, hs, hadj⟩
  · exact Or.inl (key v h)
  · exact Or.inr ⟨s, key s hs, hadj⟩
