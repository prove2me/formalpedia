-- Prove2me | solution 1 for Robbins.exists_strong_orientation_of_isEdgeConnected_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:37:08.688991+00:00
-- url     : https://prove2.me/submissions/47015968-877a-429b-9422-02bc6bcdcc2f

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux
public import Definitions.Def_RobbinsLib_Robbins
public import Theorems.Thm_Robbins_robbins

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Robbins
namespace Robbins
theorem _root_.solution {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsEdgeConnected 2) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ u v, Relation.ReflTransGen D.Adj u v := by
  refine (robbins G (hG.connected (by norm_num))).2 ?_
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [isBridge_iff_not_isEdgeReachable_two he, not_not]
    exact hG u v
end Robbins
