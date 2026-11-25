-- Prove2me | solution 1 for StrongOrientation.robbins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:39:38.751428+00:00
-- url     : https://prove2.me/submissions/99cc97ff-3d02-41a8-96eb-e14136677a99

module
public import Mathlib
public import Definitions.Def_RobbinsLib_Robbins
public import Definitions.Def_RobbinsStrongOrientation_Solution
public import Theorems.Thm_Robbins_robbins


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open StrongOrientation
namespace StrongOrientation
theorem _root_.solution {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    (∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
        ∀ u v, Relation.ReflTransGen D.Adj u v) ↔
      ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
  Robbins.robbins G hG
end StrongOrientation
