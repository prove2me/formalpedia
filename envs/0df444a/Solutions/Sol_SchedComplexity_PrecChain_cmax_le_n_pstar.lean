-- Prove2me | solution 1 for SchedComplexity.PrecChain.cmax_le_n_pstar
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:34:14.540979+00:00
-- url     : https://prove2.me/submissions/c557fd2d-6ae4-40d6-acc7-2421e172dc72

import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model



namespace SchedComplexity.PrecChain
open Classical

theorem pc_rank_exists (I : Instance) (hA : I.Acyclic) :
    ∃ r : Fin I.n → ℕ, Function.Injective r ∧ (∀ j, r j < I.n) ∧
      ∀ j k, I.Precedes j k → r j < r k := by
  -- predecessor count
  let d : Fin I.n → ℕ := fun j => (Finset.univ.filter (fun k => Relation.TransGen I.Precedes k j)).card
  have hd : ∀ j k, I.Precedes j k → d j < d k := by
    intro j k hjk
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, ?_, ?_⟩
      · simp [Relation.TransGen.single hjk]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hA j
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact Relation.TransGen.trans hx (Relation.TransGen.single hjk)
  let key : Fin I.n → ℕ := fun j => d j * I.n + j.val
  have hkey_inj : Function.Injective key := by
    intro a b h
    have hb := b.2; have ha := a.2
    have h1 : d a = d b := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h2 | h2
      · simp only [key] at h; nlinarith
      · simp only [key] at h; nlinarith
    have : a.val = b.val := by simp only [key] at h; rw [h1] at h; omega
    exact Fin.ext this
  have hkey_mono : ∀ j k, I.Precedes j k → key j < key k := by
    intro j k hjk
    have := hd j k hjk
    have hj := j.2
    simp only [key]
    nlinarith
  let r : Fin I.n → ℕ := fun j => (Finset.univ.filter (fun k => key k < key j)).card
  refine ⟨r, ?_, ?_, ?_⟩
  · intro a b h
    by_contra hne
    rcases lt_or_gt_of_ne (fun e => hne (hkey_inj e)) with h1 | h1
    · have : r a < r b := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨a, by simp [h1], by simp⟩
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; omega
      omega
    · have : r b < r a := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨b, by simp [h1], by simp⟩
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; omega
      omega
  · intro j
    have : r j < (Finset.univ : Finset (Fin I.n)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨j, Finset.mem_univ _, by simp⟩
    simpa using this
  · intro j k hjk
    have h := hkey_mono j k hjk
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j, by simp [h], by simp⟩
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; omega

theorem cmax_core (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) :
    CmaxYes I (I.n * pstar) := by
  obtain ⟨hm, hp, hA⟩ := hI
  obtain ⟨r, hinj, hlt, hmono⟩ := pc_rank_exists I hA
  refine ⟨⟨fun _ => ⟨0, hm⟩, fun j => r j * pstar⟩, ⟨?_, ?_⟩, ?_⟩
  · intro j k hjk _
    have hjk' : r j ≠ r k := fun h => hjk (hinj h)
    rcases lt_or_gt_of_ne hjk' with h | h
    · left
      show r j * pstar + I.p j ≤ r k * pstar
      have := (hp j).2
      nlinarith
    · right
      show r k * pstar + I.p k ≤ r j * pstar
      have := (hp k).2
      nlinarith
  · intro j k hjk
    have h := hmono j k hjk
    show r j * pstar + I.p j ≤ r k * pstar
    have := (hp j).2
    nlinarith
  · intro j
    show r j * pstar + I.p j ≤ I.n * pstar
    have := (hp j).2
    have := hlt j
    nlinarith

end SchedComplexity.PrecChain

open SchedComplexity.PrecChain


theorem solution (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) :
    CmaxYes I (I.n * pstar) := by
  exact cmax_core pstar I hI
