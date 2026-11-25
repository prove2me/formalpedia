-- Prove2me | solution 1 for SimpleGraph.countP_eq_degree_of_forall_adj_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:44:43.931989+00:00
-- url     : https://prove2.me/submissions/c3bfad58-d703-4e3c-bed8-399442f68ee3

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {L : List (Sym2 V)} (hL : L.Nodup)
    (hsub : ∀ e ∈ L, e ∈ G.edgeSet) {x : V} (h : ∀ y, G.Adj x y → s(x, y) ∈ L) :
    L.countP (fun e => x ∈ e) = G.degree x := by
  have hinc : G.incidenceFinset x = (⟨(L : Multiset (Sym2 V)), hL⟩ : Finset _).filter (x ∈ ·) := by
    ext e
    simp only [mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq, Finset.mem_filter]
    constructor
    · rintro ⟨he, hxe⟩
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
      exact ⟨h y he, hxe⟩
    · rintro ⟨hm, hxe⟩
      exact ⟨hsub _ hm, hxe⟩
  rw [← card_incidenceFinset_eq_degree, hinc, ← Multiset.coe_countP,
    Multiset.countP_eq_card_filter]
  rfl
end SimpleGraph
