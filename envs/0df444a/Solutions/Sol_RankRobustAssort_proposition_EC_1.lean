-- Prove2me | solution 1 for RankRobustAssort.proposition_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:59:28.747979+00:00
-- url     : https://prove2.me/submissions/5786a744-456f-43b4-8803-ed445baf9acf

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_rho
import Definitions.Def_RankRobustAssort_Ical

open Classical

namespace Aux_RRA_EC1p
open RankRobustAssort

def Syn {n : ℕ} (_R : Fin (n + 1) → Fin (n + 1) → Prop) : Type := Fin (n + 1)

def synPO {n : ℕ} (R : Fin (n + 1) → Fin (n + 1) → Prop) (hac : ∀ a, ¬ Relation.TransGen R a a) :
    PartialOrder (Syn R) where
  le x y := Relation.ReflTransGen R y x
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ hxy hyz := hyz.trans hxy
  le_antisymm x y hxy hyx := by
    by_contra hne
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxy with h | h
    · exact hne h
    · exact hac y (h.trans_left hyx)

lemma linext {n : ℕ} (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hac : ∀ a, ¬ Relation.TransGen R a a) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), ∀ a b, R a b → σ b < σ a := by
  letI : PartialOrder (Syn R) := synPO R hac
  letI : Fintype (LinearExtension (Syn R)) := inferInstanceAs (Fintype (Fin (n + 1)))
  have hcard : Fintype.card (LinearExtension (Syn R)) = n + 1 := Fintype.card_fin (n + 1)
  let e := (monoEquivOfFin (LinearExtension (Syn R)) hcard).symm
  refine ⟨e.toEquiv, fun a b hab => ?_⟩
  have hne : a ≠ b := by
    rintro rfl
    exact hac a (Relation.TransGen.single hab)
  have hle : (show Syn R from b) ≤ (show Syn R from a) := Relation.ReflTransGen.single hab
  have h1 : e (toLinearExtension (show Syn R from b)) ≤ e (toLinearExtension (show Syn R from a)) :=
    e.monotone (toLinearExtension.monotone hle)
  have h2 : e (toLinearExtension (show Syn R from b)) ≠ e (toLinearExtension (show Syn R from a)) := by
    intro h; exact hne (e.injective h).symm
  exact lt_of_le_of_ne h1 h2

end Aux_RRA_EC1p

open RankRobustAssort Aux_RRA_EC1p in
theorem solution {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) (hS : 0 ∈ S)
    (t : Fin M → Fin (n + 1)) (ht : InL P t) :
    rho P t S = (S.filter (fun i => Ical P t S i)).inf (fun i => ((P.r i : ℝ) : WithTop ℝ)) := by
  obtain ⟨σ0, hσ0⟩ := ht
  have htS : ∀ m, t m ∈ P.S m := fun m => (hσ0 m).1
  -- consistent rankings put edge targets strictly above
  have step : ∀ σ : Equiv.Perm (Fin (n + 1)), (∀ m, IsTop σ (P.S m) (t m)) →
      ∀ a b, Relation.TransGen (edge P t) a b → σ b < σ a := by
    intro σ hσ a b h
    induction h with
    | single he =>
      obtain ⟨m, ha, hne, hb⟩ := he
      rw [hb]
      exact lt_of_le_of_ne ((hσ m).2 _ ha) (fun h => hne (σ.injective h).symm)
    | tail _ he ih =>
      obtain ⟨m, ha, hne, hb⟩ := he
      rw [hb]
      exact lt_trans (lt_of_le_of_ne ((hσ m).2 _ ha) (fun h => hne (σ.injective h).symm)) ih
  have hacE : ∀ a, ¬ Relation.TransGen (edge P t) a a := by
    intro a h
    exact lt_irrefl _ (step σ0 hσ0 a a h)
  unfold rho
  congr 1
  apply Finset.filter_congr
  intro i hi
  constructor
  · rintro ⟨σ, hσ, htop⟩ m hm hreach
    have h1 := step σ hσ i (t m) hreach
    have h2 := htop.2 (t m) hm
    exact absurd h2 (not_le.2 h1)
  · intro hI
    let E' : Fin (n + 1) → Fin (n + 1) → Prop := fun a b => edge P t a b ∨ (a ∈ S ∧ a ≠ i ∧ b = i)
    have inv : ∀ a b, Relation.TransGen E' a b → Relation.TransGen (edge P t) a b ∨
        (Relation.ReflTransGen (edge P t) i b ∧ ∃ j ∈ S, j ≠ i ∧ Relation.ReflTransGen (edge P t) a j) := by
      intro a b h
      induction h with
      | single he =>
        rcases he with he | ⟨haS, hai, rfl⟩
        · exact Or.inl (Relation.TransGen.single he)
        · exact Or.inr ⟨Relation.ReflTransGen.refl, _, haS, hai, Relation.ReflTransGen.refl⟩
      | tail _ he ih =>
        rcases ih with ih | ⟨hib, j, hj, hji, haj⟩
        · rcases he with he | ⟨hcS, hci, rfl⟩
          · exact Or.inl (ih.tail he)
          · exact Or.inr ⟨Relation.ReflTransGen.refl, _, hcS, hci, ih.to_reflTransGen⟩
        · rcases he with he | ⟨hcS, hci, rfl⟩
          · exact Or.inr ⟨hib.tail he, j, hj, hji, haj⟩
          · exact Or.inr ⟨Relation.ReflTransGen.refl, j, hj, hji, haj⟩
    have hac' : ∀ a, ¬ Relation.TransGen E' a a := by
      intro a h
      rcases inv a a h with h1 | ⟨hia, j, hj, hji, haj⟩
      · exact hacE a h1
      · have hij : Relation.ReflTransGen (edge P t) i j := hia.trans haj
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 hij with h2 | h2
        · exact hji h2
        · -- the last edge of a path ends at some t m
          obtain ⟨c, _, hcj⟩ := Relation.TransGen.tail'_iff.1 h2
          obtain ⟨m, _, _, hjm⟩ := hcj
          rw [hjm] at hj h2
          exact hI m hj h2
    obtain ⟨σ, hσ⟩ := linext E' hac'
    refine ⟨σ, fun m => ⟨htS m, fun j hj => ?_⟩, hi, fun j hj => ?_⟩
    · by_cases hjt : j = t m
      · rw [hjt]
      · exact le_of_lt (hσ j (t m) (Or.inl ⟨m, hj, hjt, rfl⟩))
    · by_cases hji : j = i
      · rw [hji]
      · exact le_of_lt (hσ j i (Or.inr ⟨hj, hji, rfl⟩))
