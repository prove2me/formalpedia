-- Prove2me | solution 1 for TenChallenges.challenge_10_infiniteDegree
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:43:18.587436+00:00
-- url     : https://prove2.me/submissions/89bd4f2a-1baf-4a0f-82fe-d9858f0d4102

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Finite.Range

/-!
# Unfriendly partition games on graphs of infinite degree

Every finite partial coloring admits a legal response at a vertex with infinitely
many neighbors. Consequently, when every neighborhood is infinite, Partitioner
wins for every ordinal clock from every finite partial coloring.
-/

open SimpleGraph
open scoped Cardinal

universe u v

namespace Continuation.InfiniteDegree

open Classical

variable {V : Type u} (G : SimpleGraph V)

private lemma update_extends {f : V → Option Bool} {x : V} (hx : f x = none) (b : Bool) :
    Extends f (Function.update f x (some b)) := by
  intro y c hfy
  have hyx : y ≠ x := fun heq => by simpa [heq, hx] using hfy
  simpa only [Function.update_of_ne hyx] using hfy

private lemma finite_update {f : V → Option Bool} (hf : HasFiniteDomain f) (x : V) (b : Bool) :
    HasFiniteDomain (Function.update f x (some b)) := by
  exact (hf.insert x).subset (fun y hy => (eq_or_ne y x).elim
    (fun h => Or.inl h)
    (fun h => Or.inr (by simpa only [Set.mem_setOf_eq, Function.update_of_ne h] using hy)))

/-- A colored vertex with infinitely many neighbors can be made unfriendly by a finite extension. -/
lemma legal_response_colored {f : V → Option Bool} (hf : HasFiniteDomain f)
    (x : V) (b : Bool) (hfx : f x = some b) (hx : (G.neighborSet x).Infinite) :
    ∃ g, IsLegalResponse G f g x := by
  classical
  let D : Set V := {y | f y ≠ none}
  letI : Fintype D := hf.fintype
  have hT : (G.neighborSet x \ D).Infinite := hx.sdiff hf
  let e : D ↪ ↥(G.neighborSet x \ D) :=
    ((Fintype.equivFin D).toEmbedding.trans Fin.valEmbedding).trans (hT.natEmbedding _)
  let S : Set V := Set.range fun d : D => (e d).val
  have hSf : S.Finite := Set.finite_range _
  have hS : S ⊆ G.neighborSet x \ D := fun y ⟨d, hd⟩ => hd ▸ (e d).property
  let g : V → Option Bool := fun y => if y ∈ S then some (!b) else f y
  have hExt : Extends f g := fun y c hy =>
    (if_neg (fun hs : y ∈ S => (hS hs).2
      (show y ∈ D from fun hn => Option.some_ne_none c (hy.symm.trans hn)))).trans hy
  have hgf : HasFiniteDomain g := (hf.union hSf).subset fun y hy =>
    if h : y ∈ S then Or.inr h else Or.inl
      (show f y ≠ none from fun hn => hy ((if_neg h).trans hn))
  have hxS : x ∉ S := fun h => G.irrefl (hS h).1
  have hsame : (G.neighborSet x ∩ g ⁻¹' {some b}) ⊆ D := fun y hy =>
    if h : y ∈ S then False.elim ((Bool.not_eq_self b).mp
      (Option.some.inj ((if_pos h).symm.trans hy.2)))
    else fun hn => Option.some_ne_none b (hy.2.symm.trans ((if_neg h).trans hn))
  let E : D ↪ NeighColored G g x (some (!b)) :=
    ⟨fun d => ⟨(e d).val, (e d).property.1, if_pos ⟨d, rfl⟩⟩,
      fun d d' h => e.injective (Subtype.ext
        (congrArg (fun z : NeighColored G g x (some (!b)) => z.val) h))⟩
  exact ⟨g, hExt, hgf, b, (if_neg hxS).trans hfx,
    (Cardinal.mk_le_mk_of_subset hsame).trans ((Cardinal.le_def ..).mpr ⟨E⟩)⟩

/-- Every query at a vertex of infinite degree admits a finite legal response. -/
theorem legal_response {f : V → Option Bool} (hf : HasFiniteDomain f)
    (x : V) (hx : (G.neighborSet x).Infinite) :
    ∃ g, IsLegalResponse G f g x := by
  classical
  exact match hfx : f x with
    | some b => legal_response_colored G hf x b hfx hx
    | none =>
      let ⟨g, hg⟩ := legal_response_colored G (finite_update hf x false)
        x false (Function.update_self ..) hx
      ⟨g, ⟨fun y c hy => hg.1 y c (update_extends hfx false y c hy), hg.2⟩⟩

/-- No countability assumption is needed when all neighborhoods are infinite. -/
theorem partitionerWins_of_infinite_neighbors
    (hG : ∀ x, (G.neighborSet x).Infinite) (α : Ordinal.{v})
    {f : V → Option Bool} (hf : HasFiniteDomain f) : PartitionerWins G f α := by
  induction α using WellFoundedLT.induction generalizing f
  rename_i α ih
  rw [PartitionerWins]
  exact fun x β hβ => let ⟨g, hg⟩ := legal_response G hf x (hG x)
    ⟨g, hg, ih β hβ hg.2.1⟩

/-- Partitioner wins at every clock on a graph of infinite degree at every vertex. -/
theorem partitionerWins_empty_of_infinite_neighbors
    (hG : ∀ x, (G.neighborSet x).Infinite) (α : Ordinal.{v}) :
    PartitionerWins G (emptyPartition V) α :=
  partitionerWins_of_infinite_neighbors G hG α
    (by simp [HasFiniteDomain, emptyPartition])

end Continuation.InfiniteDegree

/-- Every finite state is winning at every clock when all neighborhoods are infinite. -/
theorem solution {V : Type u} (G : SimpleGraph V)
    (hG : ∀ x, (G.neighborSet x).Infinite) (r : Ordinal.{v})
    {f : V → Option Bool} (hf : HasFiniteDomain f) : PartitionerWins G f r :=
  Continuation.InfiniteDegree.partitionerWins_of_infinite_neighbors G hG r hf

#print axioms solution
