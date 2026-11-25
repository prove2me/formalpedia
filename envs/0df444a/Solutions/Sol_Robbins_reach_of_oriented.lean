-- Prove2me | solution 1 for Robbins.reach_of_oriented
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:23:45.880088+00:00
-- url     : https://prove2.me/submissions/1d7108cb-7f95-40ac-8dc9-2f25a52a7e37

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Robbins
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace Robbins
theorem _root_.solution {D : V → V → Prop} (h : Inv G D) {x y : V} (hxy : D x y ∨ D y x) :
    Relation.ReflTransGen D x y := by
  rcases hxy with h1 | h1
  · exact Relation.ReflTransGen.single h1
  · exact h.ret _ _ h1
end Robbins
