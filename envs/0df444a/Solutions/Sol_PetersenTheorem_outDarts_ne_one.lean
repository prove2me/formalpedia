-- Prove2me | solution 1 for PetersenTheorem.outDarts_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:12:52.850401+00:00
-- url     : https://prove2.me/submissions/8c4929a6-2c27-4e29-a17a-bda0f67ede78

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace PetersenTheorem
theorem _root_.solution (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (C : Finset V) :
    outDarts G C ≠ 1 := by
  intro h1
  have hcard : (C.sigma fun x => G.neighborFinset x \ C).card = 1 := by
    rw [Finset.card_sigma]; exact h1
  obtain ⟨⟨x, y⟩, hD⟩ := Finset.card_eq_one.mp hcard
  have hxy : (⟨x, y⟩ : Σ _ : V, V) ∈ C.sigma fun x => G.neighborFinset x \ C := by
    rw [hD]; exact Finset.mem_singleton_self _
  simp only [Finset.mem_sigma, Finset.mem_sdiff, mem_neighborFinset] at hxy
  obtain ⟨hx, hadj, hy⟩ := hxy
  apply hb s(x, y) hadj
  rw [isBridge_iff]
  rintro ⟨p⟩
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (C : Set V) hx hy
  have hdadj := d.adj
  rw [deleteEdges_adj] at hdadj
  have hmem : (⟨d.fst, d.snd⟩ : Σ _ : V, V) ∈ C.sigma fun x => G.neighborFinset x \ C := by
    simp only [Finset.mem_sigma, Finset.mem_sdiff, mem_neighborFinset]
    exact ⟨hd1, hdadj.1, hd2⟩
  rw [hD, Finset.mem_singleton] at hmem
  simp only [Sigma.mk.injEq, heq_eq_eq] at hmem
  apply hdadj.2
  rw [hmem.1, hmem.2]
  rfl
end PetersenTheorem
