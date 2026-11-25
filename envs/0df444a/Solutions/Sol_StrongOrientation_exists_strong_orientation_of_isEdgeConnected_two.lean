-- Prove2me | solution 1 for StrongOrientation.exists_strong_orientation_of_isEdgeConnected_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:43:43.792631+00:00
-- url     : https://prove2.me/submissions/2fb1e1f7-f81d-43ac-9eba-8b76297d3ef7

module
public import Mathlib
public import Definitions.Def_RobbinsLib_Robbins
public import Definitions.Def_RobbinsStrongOrientation_Solution
public import Theorems.Thm_Robbins_exists_strong_orientation_of_isEdgeConnected_two


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open StrongOrientation
namespace StrongOrientation
theorem _root_.solution {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsEdgeConnected 2) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ u v, Relation.ReflTransGen D.Adj u v :=
  Robbins.exists_strong_orientation_of_isEdgeConnected_two G hG
end StrongOrientation
