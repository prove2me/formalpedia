-- Prove2me | solution 1 for Robbins.robbins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:34:09.691263+00:00
-- url     : https://prove2.me/submissions/bd16755e-6932-4250-82fe-328fdad0eb54

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux
public import Definitions.Def_RobbinsLib_Robbins
public import Theorems.Thm_Robbins_exists_full
public import Theorems.Thm_Robbins_reach_of_oriented
public import Theorems.Thm_Robbins_reach_of_walk


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Robbins
namespace Robbins
theorem _root_.solution {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    (∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
        ∀ u v, Relation.ReflTransGen D.Adj u v) ↔
      ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by
  constructor
  · rintro ⟨Dg, hDg, hanti, hstrong⟩ e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : ∀ x y, Dg.Adj x y → G.Adj x y := by
        intro x y h
        rw [← hDg]
        simp only [Digraph.toSimpleGraphInclusive, fromRel_adj]
        exact ⟨fun hxy => hanti x y h (hxy ▸ h), Or.inl h⟩
      have huvG : G.Adj u v := he
      have hor : Dg.Adj u v ∨ Dg.Adj v u := by
        rw [← hDg] at huvG
        simp only [Digraph.toSimpleGraphInclusive, fromRel_adj] at huvG
        exact huvG.2
      -- reduce to an arc `a → b` with `s(a, b) = s(u, v)`
      suffices key : ∀ a b, Dg.Adj a b → ¬ G.IsBridge s(a, b) by
        rcases hor with h | h
        · exact key u v h
        · rw [Sym2.eq_swap]; exact key v u h
      intro a b hab
      rw [isBridge_iff, not_not]
      set H := G.deleteEdges {s(a, b)}
      have hback : ∀ x, Relation.ReflTransGen Dg.Adj x a → H.Reachable x a := by
        intro x hx
        induction hx using Relation.ReflTransGen.head_induction_on with
        | refl => exact Reachable.refl _
        | @head x y hxy _ ih =>
          by_cases hxa : x = a
          · subst hxa; exact Reachable.refl _
          · have hHxy : H.Adj x y := by
              rw [deleteEdges_adj]
              refine ⟨hadj x y hxy, ?_⟩
              intro hmem
              rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨h1, -⟩ | ⟨h1, h2⟩
              · exact hxa h1
              · subst h1; subst h2; exact hanti _ _ hab hxy
            exact hHxy.reachable.trans ih
      exact (hback b (hstrong b a)).symm
  · intro hb
    obtain ⟨D, hI, hcov⟩ := Robbins.exists_full hb
    refine ⟨⟨D⟩, ?_, hI.anti, ?_⟩
    · ext a b
      simp only [Digraph.toSimpleGraphInclusive, fromRel_adj]
      constructor
      · rintro ⟨-, h | h⟩
        · exact hI.sub _ _ h
        · exact (hI.sub _ _ h).symm
      · intro h
        exact ⟨G.ne_of_adj h, hcov a b h⟩
    · intro a b
      obtain ⟨w⟩ := hG.preconnected a b
      exact reach_of_walk w fun d _ => reach_of_oriented hI (hcov _ _ d.adj)
end Robbins
