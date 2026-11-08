-- Prove2me | solution 1 for RankRobustAssort.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:34:47.532795+00:00
-- url     : https://prove2.me/submissions/ced1c490-90fb-45ab-a4b9-b29319d55ffb

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Acyclic

namespace Aux_RRA_EC1
open RankRobustAssort

def Syn {n M : ℕ} (_P : Problem n M) (_t : Fin M → Fin (n + 1)) : Type := Fin (n + 1)

def synPO {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (hac : Acyclic P t) :
    PartialOrder (Syn P t) where
  le x y := Relation.ReflTransGen (edge P t) y x
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ hxy hyz := hyz.trans hxy
  le_antisymm x y hxy hyx := by
    by_contra hne
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxy with h | h
    · exact hne h
    · exact hac y (h.trans_left hyx)

end Aux_RRA_EC1

open RankRobustAssort Aux_RRA_EC1 in
theorem solution {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1))
    (ht : ∀ m, t m ∈ P.S m) :
    InL P t ↔ Acyclic P t := by
  constructor
  · rintro ⟨σ, hσ⟩ a hcyc
    have step : ∀ a b, edge P t a b → σ b < σ a := by
      rintro a b ⟨m, ha, hne, hb⟩
      rw [hb]
      exact lt_of_le_of_ne ((hσ m).2 _ ha) (fun h => hne (σ.injective h).symm)
    have key : ∀ a b, Relation.TransGen (edge P t) a b → σ b < σ a := by
      intro a b h
      induction h with
      | single he => exact step _ _ he
      | tail _ he ih => exact lt_trans (step _ _ he) ih
    exact lt_irrefl _ (key a a hcyc)
  · intro hac
    letI : PartialOrder (Syn P t) := synPO P t hac
    letI : Fintype (LinearExtension (Syn P t)) := inferInstanceAs (Fintype (Fin (n + 1)))
    have hcard : Fintype.card (LinearExtension (Syn P t)) = n + 1 := Fintype.card_fin (n + 1)
    let e := (monoEquivOfFin (LinearExtension (Syn P t)) hcard).symm
    let σ : Equiv.Perm (Fin (n + 1)) := e.toEquiv
    have hlt : ∀ a b, edge P t a b → σ b < σ a := by
      intro a b hab
      have hne : a ≠ b := by
        rintro rfl
        exact hac a (Relation.TransGen.single hab)
      have hle : (show Syn P t from b) ≤ (show Syn P t from a) :=
        Relation.ReflTransGen.single hab
      have h1 : e (toLinearExtension (show Syn P t from b)) ≤
          e (toLinearExtension (show Syn P t from a)) :=
        e.monotone (toLinearExtension.monotone hle)
      have h2 : e (toLinearExtension (show Syn P t from b)) ≠
          e (toLinearExtension (show Syn P t from a)) := by
        intro h
        exact hne (e.injective h).symm
      exact lt_of_le_of_ne h1 h2
    refine ⟨σ, fun m => ⟨ht m, fun j hj => ?_⟩⟩
    by_cases hjt : j = t m
    · rw [hjt]
    · exact le_of_lt (hlt j (t m) ⟨m, hj, hjt, rfl⟩)
