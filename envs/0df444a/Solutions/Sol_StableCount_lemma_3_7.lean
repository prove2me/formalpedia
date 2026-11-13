-- Prove2me | solution 1 for StableCount.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:15:57.846507+00:00
-- url     : https://prove2.me/submissions/fc3368c9-3dcb-4d7b-95ef-72e944458959

import Mathlib
import Theorems.Thm_StableCount_lemma_3_6

section
namespace StableCount

open StableMatching

namespace Dev.L37

open Classical

variable {n : ℕ}

theorem mem_down (Q : Member n) (i j : Fin Q.R) : j ∈ Q.down i ↔ Q.le j i := by
  simp [Member.down]

theorem mem_up (Q : Member n) (i j : Fin Q.R) : j ∈ Q.up i ↔ Q.le i j := by
  simp [Member.up]

theorem le_refl' (Q : Member n) (i : Fin Q.R) : Q.le i i := Relation.ReflTransGen.refl

theorem le_trans' (Q : Member n) {a b c : Fin Q.R} (h1 : Q.le a b) (h2 : Q.le b c) : Q.le a c :=
  Relation.ReflTransGen.trans h1 h2

theorem isDownset_down (Q : Member n) (i : Fin Q.R) : Q.IsDownsetIn Finset.univ (Q.down i) := by
  refine ⟨Finset.subset_univ _, fun a ha b _ hba => ?_⟩
  rw [mem_down] at ha ⊢
  exact le_trans' Q hba ha

theorem isUpset_up (Q : Member n) (i : Fin Q.R) : Q.IsUpset (Q.up i) := by
  intro a ha b hab
  rw [mem_up] at ha ⊢
  exact le_trans' Q ha hab

theorem not_mem_case (Q : Member n) (i : Fin Q.R) :
    ((Finset.univ : Finset (Fin Q.R)).powerset.filter fun D => Q.IsDownsetIn Finset.univ D).filter
        (fun D => i ∉ D) =
      (Finset.univ \ Q.up i).powerset.filter fun D => Q.IsDownsetIn (Finset.univ \ Q.up i) D := by
  ext D
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨-, hD⟩, hi⟩
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_up]
      intro hib
      exact hi (hD.2 b hb i (Finset.mem_univ _) hib)
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_up]
      intro hib
      exact hi (hD.2 b hb i (Finset.mem_univ _) hib)
    · intro a ha b hb hba
      exact hD.2 a ha b (Finset.mem_univ _) hba
  · rintro ⟨hsub, -, hD2⟩
    have hDd : Q.IsDownsetIn Finset.univ D := by
      refine ⟨Finset.subset_univ _, fun a ha b _ hba => ?_⟩
      by_contra hb
      have haU := hsub ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_up] at haU
      have hbU : b ∈ Finset.univ \ Q.up i := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_up]
        intro hib
        exact haU (le_trans' Q hib hba)
      exact hb (hD2 a ha b hbU hba)
    refine ⟨⟨Finset.subset_univ _, hDd⟩, ?_⟩
    intro hi
    have := hsub hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_up] at this
    exact this (le_refl' Q i)

theorem mem_case (Q : Member n) (i : Fin Q.R) :
    (((Finset.univ : Finset (Fin Q.R)).powerset.filter fun D => Q.IsDownsetIn Finset.univ D).filter
        (fun D => i ∈ D)).card =
      ((Finset.univ \ Q.down i).powerset.filter fun D => Q.IsDownsetIn (Finset.univ \ Q.down i) D).card := by
  refine Finset.card_nbij' (fun D => D \ Q.down i) (fun K => K ∪ Q.down i) ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq, Finset.mem_filter] at hD ⊢
    obtain ⟨⟨-, hDd⟩, hi⟩ := hD
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb ⊢
      exact hb.2
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb ⊢
      exact hb.2
    · intro a ha b hb hba
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb ⊢
      exact ⟨hDd.2 a ha.1 b (Finset.mem_univ _) hba, hb⟩
  · intro K hK
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq, Finset.mem_filter] at hK ⊢
    obtain ⟨hsub, -, hK2⟩ := hK
    refine ⟨⟨Finset.subset_univ _, Finset.subset_univ _, ?_⟩, ?_⟩
    · intro a ha b _ hba
      rcases Finset.mem_union.mp ha with ha | ha
      · by_cases hb : b ∈ Q.down i
        · exact Finset.mem_union_right _ hb
        · have hbm : b ∈ Finset.univ \ Q.down i := by simp [hb]
          exact Finset.mem_union_left _ (hK2 a ha b hbm hba)
      · rw [mem_down] at ha
        exact Finset.mem_union_right _ ((mem_down Q i b).mpr (le_trans' Q hba ha))
    · exact Finset.mem_union_right _ ((mem_down Q i i).mpr (le_refl' Q i))
  · intro D hD
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq, Finset.mem_filter] at hD
    obtain ⟨⟨-, hDd⟩, hi⟩ := hD
    refine Finset.sdiff_union_of_subset ?_
    intro b hb
    rw [mem_down] at hb
    exact hDd.2 i hi b (Finset.mem_univ _) hb
  · intro K hK
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq, Finset.mem_filter] at hK
    obtain ⟨hsub, -, -⟩ := hK
    refine Finset.union_sdiff_cancel_right ?_
    exact Finset.disjoint_left.mpr fun x hx hx2 => (Finset.mem_sdiff.mp (hsub hx)).2 hx2

theorem Jon_split (Q : Member n) (i : Fin Q.R) :
    Q.Jon Finset.univ = Q.Jon (Finset.univ \ Q.down i) + Q.Jon (Finset.univ \ Q.up i) := by
  unfold Member.Jon
  rw [← Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin Q.R)).powerset.filter
      fun D => Q.IsDownsetIn Finset.univ D) (fun D => i ∈ D), mem_case, not_mem_case]

theorem Jon_restriction (Q Q' : Member n) (P : Finset (Fin Q.R))
    (e : {i // i ∈ P} ≃ Fin Q'.R) (he : Q.IsRestriction P Q' e) : Q'.J = Q.Jon P := by
  unfold Member.J Member.Jon
  refine Finset.card_nbij'
    (fun K => (Finset.univ : Finset (Fin Q.R)).filter fun a => ∃ h : a ∈ P, e ⟨a, h⟩ ∈ K)
    (fun D => (Finset.univ : Finset (Fin Q'.R)).filter fun j => (e.symm j).1 ∈ D) ?_ ?_ ?_ ?_
  · intro K hK
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq, Finset.mem_filter] at hK ⊢
    obtain ⟨-, -, hK2⟩ := hK
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_filter] at ha
      exact ha.2.1
    · intro a ha
      simp only [Finset.mem_filter] at ha
      exact ha.2.1
    · intro a ha b hb hba
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      obtain ⟨haP, haK⟩ := ha
      refine ⟨hb, ?_⟩
      have := (he.1 ⟨b, hb⟩ ⟨a, haP⟩).mp hba
      exact hK2 _ haK _ (Finset.mem_univ _) this
  · intro D hD
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq, Finset.mem_filter] at hD ⊢
    obtain ⟨-, -, hD2⟩ := hD
    refine ⟨Finset.subset_univ _, Finset.subset_univ _, ?_⟩
    intro j hj j' _ hjj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have h1 : Q.le (e.symm j') (e.symm j) := by
      rw [he.1]; simpa using hjj'
    exact hD2 _ hj _ (e.symm j').2 h1
  · intro K _
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hk⟩
      simpa using hk
    · intro hj
      refine ⟨(e.symm j).2, ?_⟩
      simpa using hj
  · intro D hD
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq, Finset.mem_filter] at hD
    obtain ⟨hsub, -, -⟩ := hD
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hh⟩
      simpa using hh
    · intro ha
      exact ⟨hsub ha, by simpa using ha⟩

theorem deg_restriction (Q Q' : Member n) (P : Finset (Fin Q.R))
    (e : {i // i ∈ P} ≃ Fin Q'.R) (he : Q.IsRestriction P Q' e) (s : Sex) (p : Fin n) :
    Q'.deg s p = Q.degOn P s p := by
  unfold Member.deg Member.degOn
  refine Finset.card_bij (fun j _ => (e.symm j).1) ?_ ?_ ?_
  · intro j hj
    simp only [Member.chainOf, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter] at hj ⊢
    refine ⟨(e.symm j).2, ?_⟩
    have := (he.2 s p (e.symm j)).mp
    simpa using this (by simpa using hj)
  · intro j _ j' _ hjj'
    exact e.symm.injective (Subtype.ext hjj')
  · intro a ha
    simp only [Member.chainOf, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter] at ha
    refine ⟨e ⟨a, ha.1⟩, ?_, by simp⟩
    simp only [Member.chainOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (he.2 s p ⟨a, ha.1⟩).mpr ha.2

theorem restr_of (Q : Member n) (D U : Finset (Fin Q.R)) (hD : Q.IsDownsetIn Finset.univ D)
    (hU : Q.IsUpset U) (hDU : Disjoint D U) (P : Finset (Fin Q.R))
    (hP : P = Finset.univ \ (D ∪ U)) :
    ∃ (QP : Member n) (e : {j // j ∈ P} ≃ Fin QP.R), Q.IsRestriction P QP e := by
  subst hP
  obtain ⟨QP, e, r, -⟩ := lemma_3_6 Q D U hD hU hDU
  exact ⟨QP, e, r⟩

end Dev.L37

theorem chk_lemma_3_7 {n : ℕ} (Q : Member n) (i : Fin Q.R) :
    Q.J = Q.Jon (Finset.univ \ Q.down i) + Q.Jon (Finset.univ \ Q.up i) ∧
    ∃ (Q₁ Q₂ : Member n) (e₁ : {j // j ∈ Finset.univ \ Q.down i} ≃ Fin Q₁.R)
      (e₂ : {j // j ∈ Finset.univ \ Q.up i} ≃ Fin Q₂.R),
      Q.IsRestriction (Finset.univ \ Q.down i) Q₁ e₁ ∧
      Q.IsRestriction (Finset.univ \ Q.up i) Q₂ e₂ ∧
      Q₁.J = Q.Jon (Finset.univ \ Q.down i) ∧ Q₂.J = Q.Jon (Finset.univ \ Q.up i) ∧
      (∀ s p, Q₁.deg s p = Q.degOn (Finset.univ \ Q.down i) s p) ∧
      ∀ s p, Q₂.deg s p = Q.degOn (Finset.univ \ Q.up i) s p := by
  refine ⟨Dev.L37.Jon_split Q i, ?_⟩
  obtain ⟨Q₁, e₁, r₁⟩ := Dev.L37.restr_of Q (Q.down i) ∅ (Dev.L37.isDownset_down Q i)
    (by intro a ha; simp at ha) (Finset.disjoint_empty_right _) (Finset.univ \ Q.down i)
    (by simp)
  obtain ⟨Q₂, e₂, r₂⟩ := Dev.L37.restr_of Q ∅ (Q.up i)
    ⟨Finset.subset_univ _, fun a ha => by simp at ha⟩ (Dev.L37.isUpset_up Q i)
    (Finset.disjoint_empty_left _) (Finset.univ \ Q.up i) (by simp)
  exact ⟨Q₁, Q₂, e₁, e₂, r₁, r₂, Dev.L37.Jon_restriction Q Q₁ _ e₁ r₁,
    Dev.L37.Jon_restriction Q Q₂ _ e₂ r₂, Dev.L37.deg_restriction Q Q₁ _ e₁ r₁,
    Dev.L37.deg_restriction Q Q₂ _ e₂ r₂⟩

end StableCount
end

theorem solution : type_of% @StableCount.chk_lemma_3_7 := @StableCount.chk_lemma_3_7
