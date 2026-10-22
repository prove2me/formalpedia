-- Prove2me | solution 1 for P7ThreeColor.Seed.p5_case
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:13:21.33751+00:00
-- url     : https://prove2.me/submissions/d38351d6-5579-473e-9764-d5b34d4bb4c7

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
    (G : SimpleGraph V) (S : Finset V)
    (hS : IsDominating G S) (hSconn : (G.induce (S : Set V)).Connected)
    (e : G.induce (S : Set V) ≃g SimpleGraph.pathGraph 5) :
    ∃ T : Finset V, T.card = 3 ∧ T ⊆ S ∧
      (G.induce (T : Set V)).Connected ∧ IsTwoDominating G T := by
  set g : Fin 5 → V := fun i => (e.symm i).1 with hg
  have hgS : ∀ i, g i ∈ S := fun i => Finset.mem_coe.1 (e.symm i).2
  have hginj : Function.Injective g := by
    intro i j hij
    have : e.symm i = e.symm j := Subtype.ext hij
    exact e.symm.injective this
  have hgadj : ∀ i j, (SimpleGraph.pathGraph 5).Adj i j → G.Adj (g i) (g j) := by
    intro i j h
    have := e.symm.map_rel_iff.2 h
    simpa [hg] using this
  have hgsurj : ∀ v ∈ S, ∃ i, g i = v := by
    intro v hv
    refine ⟨e ⟨v, by simpa using hv⟩, ?_⟩
    simp [hg]
  have a01 : G.Adj (g 0) (g 1) := hgadj 0 1 (by simp [SimpleGraph.pathGraph_adj])
  have a12 : G.Adj (g 1) (g 2) := hgadj 1 2 (by simp [SimpleGraph.pathGraph_adj])
  have a23 : G.Adj (g 2) (g 3) := hgadj 2 3 (by simp [SimpleGraph.pathGraph_adj])
  have a34 : G.Adj (g 3) (g 4) := hgadj 3 4 (by simp [SimpleGraph.pathGraph_adj])
  refine ⟨{g 1, g 2, g 3}, ?_, ?_, ?_, ?_⟩
  · apply Finset.card_eq_three.2
    refine ⟨g 1, g 2, g 3, ?_, ?_, ?_, rfl⟩
    · intro h; have := hginj h; simp at this
    · intro h; have := hginj h; simp at this
    · intro h; have := hginj h; simp at this
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact hgS _
  · -- connectivity
    let T : Finset V := {g 1, g 2, g 3}
    have hmem : ∀ i : Fin 3, g ⟨i.val + 1, by omega⟩ ∈ (T : Set V) := by
      intro i
      fin_cases i <;> simp [T]
    let f : (SimpleGraph.pathGraph 3) →g G.induce (T : Set V) :=
      ⟨fun i => ⟨g ⟨i.val + 1, by omega⟩, hmem i⟩, by
        intro i j h
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
        apply hgadj
        rw [SimpleGraph.pathGraph_adj] at h ⊢
        simp only [Fin.val_mk]
        omega⟩
    have hsurj : ∀ x : (T : Set V), ∃ i, f i = x := by
      rintro ⟨x, hx⟩
      have hx' : x = g 1 ∨ x = g 2 ∨ x = g 3 := by simpa [T] using hx
      rcases hx' with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    haveI : Nonempty (T : Set V) := ⟨⟨g 1, hmem 0⟩⟩
    refine ⟨?_⟩
    intro x y
    obtain ⟨i, rfl⟩ := hsurj x
    obtain ⟨j, rfl⟩ := hsurj y
    exact ((SimpleGraph.pathGraph_preconnected 3) i j).map f
  · have hsub : ∀ v ∈ S, v ∈ P7ThreeColor.Seed.closure G {g 1, g 2, g 3} := by
      intro v hv
      obtain ⟨i, rfl⟩ := hgsurj v hv
      rw [mem_cl]
      fin_cases i
      · exact Or.inr ⟨g 1, by simp, a01⟩
      · exact Or.inl (by simp)
      · exact Or.inl (by simp)
      · exact Or.inl (by simp)
      · exact Or.inr ⟨g 3, by simp, a34.symm⟩
    have hS' : ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj v s := by
      intro v
      have : v ∈ P7ThreeColor.Seed.closure G S := by
        have h : P7ThreeColor.Seed.closure G S = Finset.univ := hS
        rw [h]; exact Finset.mem_univ v
      exact (mem_cl G S v).1 this
    unfold IsTwoDominating IsDominating
    apply Finset.eq_univ_of_forall
    intro v
    rw [mem_cl]
    rcases hS' v with h | ⟨s, hs, hadj⟩
    · exact Or.inl (hsub v h)
    · exact Or.inr ⟨s, hsub s hs, hadj⟩
