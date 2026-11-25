-- Prove2me | solution 1 for Robbins.extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:27:23.551825+00:00
-- url     : https://prove2.me/submissions/ed699835-bc5f-4688-8241-511cc3c24220

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux
public import Theorems.Thm_Robbins_reach_of_walk
public import Theorems.Thm_Robbins_not_rev_of_isPath

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Robbins
variable {V : Type*} (G : SimpleGraph V)
variable {G}
open Classical
namespace Robbins
theorem _root_.solution {D : V → V → Prop} (hI : Inv G D) {u v : V} (huv : G.Adj u v) (hnu : ¬ D u v)
    (hnv : ¬ D v u) (hnb : ¬ G.IsBridge s(u, v)) :
    ∃ D' : V → V → Prop, Inv G D' ∧ (∀ a b, D a b → D' a b) ∧ D' u v := by
  set H := G.deleteEdges {s(u, v)} with hH
  have hreach : H.Reachable u v := by
    by_contra h
    exact hnb (isBridge_iff.mpr h)
  obtain ⟨q, hq⟩ := (Classical.choice hreach.symm).toPath
  -- the darts of the path
  have hdart : ∀ d ∈ q.darts, G.Adj d.fst d.snd ∧ s(d.fst, d.snd) ≠ s(u, v) := by
    intro d _
    have h : G.Adj d.fst d.snd ∧ s(d.fst, d.snd) ∉ ({s(u, v)} : Set (Sym2 V)) :=
      deleteEdges_adj.mp d.adj
    exact ⟨h.1, by simpa using h.2⟩
  let N : V → V → Prop := fun a b => ∃ d ∈ q.darts, d.fst = a ∧ d.snd = b
  let D' : V → V → Prop := fun a b =>
    D a b ∨ (a = u ∧ b = v) ∨ (N a b ∧ ¬ D a b ∧ ¬ D b a)
  have hND : ∀ a b, N a b → G.Adj a b ∧ s(a, b) ≠ s(u, v) := by
    rintro a b ⟨d, hd, rfl, rfl⟩
    exact hdart d hd
  have hNuv : ¬ N v u := by
    intro h
    exact (hND v u h).2 Sym2.eq_swap
  have hmono : ∀ a b, D a b → D' a b := fun a b h => Or.inl h
  -- every dart of the path is traversable in `D'`
  have hdartR : ∀ d ∈ q.darts, Relation.ReflTransGen D' d.fst d.snd := by
    intro d hd
    by_cases h1 : D d.fst d.snd
    · exact Relation.ReflTransGen.single (Or.inl h1)
    by_cases h2 : D d.snd d.fst
    · exact Relation.ReflTransGen.mono hmono _ _ (hI.ret _ _ h2)
    · exact Relation.ReflTransGen.single (Or.inr (Or.inr ⟨⟨d, hd, rfl, rfl⟩, h1, h2⟩))
  have hvu : Relation.ReflTransGen D' v u := reach_of_walk q hdartR
  have hvx : ∀ x ∈ q.support, Relation.ReflTransGen D' v x := fun x hx =>
    reach_of_walk (q.takeUntil x hx) fun d hd =>
      hdartR d (Walk.darts_takeUntil_subset_darts q hx hd)
  have hxu : ∀ x ∈ q.support, Relation.ReflTransGen D' x u := fun x hx =>
    reach_of_walk (q.dropUntil x hx) fun d hd =>
      hdartR d (Walk.darts_dropUntil_subset_darts q hx hd)
  refine ⟨D', ⟨?_, ?_, ?_⟩, hmono, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · rintro a b (h | ⟨rfl, rfl⟩ | ⟨h, -, -⟩)
    · exact hI.sub _ _ h
    · exact huv
    · exact (hND a b h).1
  · intro a b h h'
    rcases h with h | ⟨ha, hb⟩ | ⟨h, h1, h2⟩ <;>
      rcases h' with h' | ⟨ha', hb'⟩ | ⟨h', h1', h2'⟩
    · exact hI.anti _ _ h h'
    · subst ha' hb'; exact hnv h
    · exact h2' h
    · subst ha hb; exact hnv h'
    · subst ha hb; exact G.ne_of_adj huv ha'.symm
    · subst ha hb; exact hNuv h'
    · exact h2 h'
    · subst ha' hb'; exact hNuv h
    · obtain ⟨d₁, hd₁, hf₁, hs₁⟩ := h
      obtain ⟨d₂, hd₂, hf₂, hs₂⟩ := h'
      exact not_rev_of_isPath hq hd₁ hd₂ (hf₁.trans hs₂.symm) (hs₁.trans hf₂.symm)
  · rintro a b (h | ⟨rfl, rfl⟩ | ⟨h, -, -⟩)
    · exact Relation.ReflTransGen.mono hmono _ _ (hI.ret _ _ h)
    · exact hvu
    · obtain ⟨d, hd, rfl, rfl⟩ := h
      have ha := Walk.dart_fst_mem_support_of_mem_darts q hd
      have hb := Walk.dart_snd_mem_support_of_mem_darts q hd
      exact ((hxu _ hb).tail (Or.inr (Or.inl ⟨rfl, rfl⟩))).trans (hvx _ ha)
end Robbins
