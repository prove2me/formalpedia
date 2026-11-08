-- Prove2me | solution 1 for ProcNetStab.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:17:04.450044+00:00
-- url     : https://prove2.me/submissions/e121ac01-cfad-4640-bdb2-90fa83db06ca

import Mathlib
import Definitions.Def_ProcNetStab_IsAcyclic

namespace Aux_ProcNetStab_t3

def Syn {X : Type*} (_R : X → X → Prop) : Type _ := X

def synPre {X : Type*} (R : X → X → Prop) : Preorder (Syn R) where
  le x y := Relation.ReflTransGen R x y
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ h1 h2 := h1.trans h2

end Aux_ProcNetStab_t3

open ProcNetStab Aux_ProcNetStab_t3 in
theorem solution {X : Type*} (R P : X → X → Prop) (hPR : ∀ x y, P x y → R x y) :
    (∃ W : X → X → Prop, IsWeakOrder W ∧ IsOrderPairExtension W R P) ↔ IsAcyclic R P := by
  constructor
  · rintro ⟨W, ⟨hcomp, htrans⟩, hRW, hPW⟩ x y hxy hPyx
    have hstar : ∀ a b, Relation.ReflTransGen R a b → W a b := by
      intro a b h
      induction h with
      | refl => exact (hcomp a a).elim id id
      | tail _ hbc ih => exact htrans _ _ _ ih (hRW _ _ hbc)
    exact (hPW y x hPyx).2 (hstar x y hxy)
  · intro hac
    letI : Preorder (Syn R) := synPre R
    let f : X → LinearExtension (Antisymmetrization (Syn R) (· ≤ ·)) :=
      fun x => toLinearExtension (toAntisymmetrization (· ≤ ·) (show Syn R from x))
    have hmono : ∀ x y, Relation.ReflTransGen R x y → f x ≤ f y := by
      intro x y h
      apply toLinearExtension.monotone
      exact (toAntisymmetrization_le_toAntisymmetrization_iff).2 h
    refine ⟨fun x y => f x ≤ f y, ⟨fun x y => le_total _ _, fun x y z h1 h2 => le_trans h1 h2⟩,
      fun x y h => hmono x y (Relation.ReflTransGen.single h), fun x y h => ⟨?_, ?_⟩⟩
    · exact hmono x y (Relation.ReflTransGen.single (hPR x y h))
    · intro hyx
      have hxy := hmono x y (Relation.ReflTransGen.single (hPR x y h))
      have heq : f x = f y := le_antisymm hxy hyx
      have heq' : toAntisymmetrization (· ≤ ·) (show Syn R from x)
          = toAntisymmetrization (· ≤ ·) (show Syn R from y) := heq
      have hle : toAntisymmetrization (· ≤ ·) (show Syn R from y)
          ≤ toAntisymmetrization (· ≤ ·) (show Syn R from x) := le_of_eq heq'.symm
      have hyx' : Relation.ReflTransGen R y x :=
        (toAntisymmetrization_le_toAntisymmetrization_iff).1 hle
      exact hac y x hyx' h
