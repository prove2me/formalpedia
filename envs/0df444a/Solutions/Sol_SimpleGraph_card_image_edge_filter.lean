-- Prove2me | solution 1 for SimpleGraph.card_image_edge_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:38:42.382907+00:00
-- url     : https://prove2.me/submissions/39afc7cc-9828-47b6-b676-60432a3be3d4

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {Ds : Finset G.Dart} (hinj : EdgeInj Ds) (v : V) :
    ((Ds.image Dart.edge).filter (v ∈ ·)).card =
      (Ds.filter fun d => d.fst = v).card + (Ds.filter fun d => d.snd = v).card := by
  have h1 : (Ds.image Dart.edge).filter (v ∈ ·) = (Ds.filter fun d => v ∈ d.edge).image Dart.edge := by
    ext e
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hv⟩; exact ⟨a, ⟨ha, hv⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hv⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, hv⟩
  rw [h1, card_image_of_injOn fun d hd d' hd' h =>
    hinj d (mem_filter.mp hd).1 d' (mem_filter.mp hd').1 h]
  have h2 : (Ds.filter fun d => v ∈ d.edge) =
      (Ds.filter fun d => d.fst = v) ∪ (Ds.filter fun d => d.snd = v) := by
    ext d
    simp only [mem_filter, mem_union, Dart.edge, Sym2.mem_iff]
    constructor
    · rintro ⟨hd, h | h⟩
      · exact Or.inl ⟨hd, h.symm⟩
      · exact Or.inr ⟨hd, h.symm⟩
    · rintro (⟨hd, h⟩ | ⟨hd, h⟩)
      · exact ⟨hd, Or.inl h.symm⟩
      · exact ⟨hd, Or.inr h.symm⟩
  rw [h2, card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro d h1 h2
  rw [mem_filter] at h1 h2
  exact d.adj.ne (h1.2.trans h2.2.symm)
end SimpleGraph
