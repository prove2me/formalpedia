-- Prove2me | solution 1 for Robbins.reach_of_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:23:40.206483+00:00
-- url     : https://prove2.me/submissions/c02e8475-17b2-4c01-a5be-5d531502ac11

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
theorem _root_.solution {H : SimpleGraph V} {D : V → V → Prop} :
    ∀ {a b : V} (p : H.Walk a b), (∀ d ∈ p.darts, Relation.ReflTransGen D d.fst d.snd) →
      Relation.ReflTransGen D a b
  | _, _, .nil, _ => Relation.ReflTransGen.refl
  | _, _, .cons h p, hd => by
      have h1 := hd ⟨(_, _), h⟩ (by simp)
      exact h1.trans (solution p fun d hd' => hd d (by simp [hd']))
end Robbins
