-- Prove2me | solution 1 for PrefSemimetric.TopDiff.dmu_axiom3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:08:13.212751+00:00
-- url     : https://prove2.me/submissions/7097af9b-b263-483b-8d83-303609a78fa8

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

theorem ps_acyclic_of_rank {X : Type*} (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (f : X → ℕ) (hf : ∀ x y, asymmPart R x y → f x < f y) : IsAcyclicOrder R := by
  refine ⟨hrefl, ?_⟩
  intro x hx
  have key : ∀ y z, Relation.TransGen (asymmPart R) y z → f y < f z := by
    intro y z h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact lt_trans ih (hf _ _ h)
  exact lt_irrefl _ (key x x hx)

theorem ps_asymm_AB {X : Type*} (a b : X) (hab : a ≠ b) (y x : X) :
    asymmPart (prefAB a b) y x ↔ (y ≠ a ∧ y ≠ b ∧ (x = a ∨ x = b)) := by
  simp only [asymmPart, prefAB]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : x = a <;> by_cases h4 : x = b <;>
    simp_all [eq_comm]

theorem ps_asymm_ABplus {X : Type*} (a b : X) (hab : a ≠ b) (y x : X) :
    asymmPart (prefABplus a b) y x ↔ ((y ≠ a ∧ y ≠ b ∧ (x = a ∨ x = b)) ∨ (y = a ∧ x = b)) := by
  simp only [asymmPart, prefABplus, prefAB]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : x = a <;> by_cases h4 : x = b <;>
    simp_all [eq_comm]

theorem ps_eq8 {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (a b : X) (hab : a ≠ b) :
    IsAcyclicOrder (prefAB a b) ∧ IsAcyclicOrder (prefABplus a b) ∧
      Dmu w (prefAB a b) (prefABplus a b) = w b := by
  classical
  let f : X → ℕ := fun x => if x = b then 2 else if x = a then 1 else 0
  refine ⟨?_, ?_, ?_⟩
  · apply ps_acyclic_of_rank (prefAB a b) (fun x => Or.inl rfl) f
    intro y x h
    rw [ps_asymm_AB a b hab] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases h3 with rfl | rfl <;> simp [f, h1, h2, hab, Ne.symm hab]
  · apply ps_acyclic_of_rank (prefABplus a b) (fun x => Or.inl (Or.inl rfl)) f
    intro y x h
    rw [ps_asymm_ABplus a b hab] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩
    · rcases h3 with rfl | rfl <;> simp [f, h1, h2, hab, Ne.symm hab]
    · simp [f, hab, Ne.symm hab]
  · have hdiff : ∀ S : Finset X, symmDiff (maxSet S (prefAB a b)) (maxSet S (prefABplus a b)) =
        if S = {a, b} then {b} else ∅ := by
      intro S
      have hSab : S = {a, b} ↔ (a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, y = a ∨ y = b) := by
        constructor
        · rintro rfl; simp
        · rintro ⟨ha, hb, hall⟩
          ext y; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact hall y
          · rintro (rfl | rfl) <;> assumption
      ext x
      simp only [Finset.mem_symmDiff, maxSet, Finset.mem_filter, ps_asymm_AB a b hab,
        ps_asymm_ABplus a b hab]
      split_ifs with hS
      · rw [hSab] at hS
        obtain ⟨ha, hb, hall⟩ := hS
        simp only [Finset.mem_singleton]
        constructor
        · rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
          · by_contra hxb
            apply hn
            refine ⟨hx, fun y hy hc => ?_⟩
            rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
            · rcases hall y hy with h' | h' <;> simp_all
            · exact hxb h2
          · exfalso; apply hn; refine ⟨hx, fun y hy hc => h y hy (Or.inl hc)⟩
        · rintro rfl
          left
          refine ⟨⟨hb, fun y hy hc => ?_⟩, fun hc => ?_⟩
          · rcases hall y hy with h' | h' <;> simp_all
          · exact hc.2 a ha (Or.inr ⟨rfl, rfl⟩)
      · rw [hSab] at hS
        simp only [Finset.notMem_empty, iff_false]
        rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
        · apply hn
          refine ⟨hx, fun y hy hc => ?_⟩
          rcases hc with hc | ⟨rfl, rfl⟩
          · exact h y hy hc
          · apply hS
            refine ⟨hy, hx, fun z hz => ?_⟩
            by_contra hzab
            push_neg at hzab
            exact h z hz ⟨hzab.1, hzab.2, Or.inr rfl⟩
        · exact hn ⟨hx, fun y hy hc => h y hy (Or.inl hc)⟩
    unfold Dmu
    simp only [hdiff]
    rw [Finset.sum_eq_single ({a, b} : Finset X)]
    · simp
    · intro S _ hS; simp [hS]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem ps_mem_max {X : Type*} (S : Finset X) (R : X → X → Prop) (x : X) :
    x ∈ maxSet S R ↔ x ∈ S ∧ ∀ y ∈ S, ¬ asymmPart R y x := by
  unfold maxSet; simp [Finset.mem_filter]

theorem ps_count {X : Type*} [Fintype X] [DecidableEq X] (a b : X) (F : Finset X)
    (haF : a ∉ F) (hbF : b ∉ F) (P : Finset X → Prop) [DecidablePred P]
    (hP : ∀ S, P S ↔ a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, y ≠ a → y ≠ b → y ∈ F) :
    (Finset.univ.filter P).card = 2 ^ F.card := by
  have heq : Finset.univ.filter P = F.powerset.image (fun U => insert a (insert b U)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · rintro ⟨ha, hb, hS⟩
      refine ⟨(S.erase a).erase b, ?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_erase] at hy
        exact hS y hy.2.2 hy.2.1 hy.1
      · ext y
        simp only [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨_, _, hy⟩) <;> assumption
        · intro hy
          by_cases h1 : y = a
          · exact Or.inl h1
          · by_cases h2 : y = b
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr ⟨h2, h1, hy⟩)
    · rintro ⟨U, hU, rfl⟩
      refine ⟨by simp, by simp, ?_⟩
      intro y hy h1 h2
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | rfl | hy
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact hU hy
  rw [heq, Finset.card_image_of_injOn, Finset.card_powerset]
  intro U hU V hV h
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hU hV
  have hUa : a ∉ U := fun h => haF (hU h)
  have hUb : b ∉ U := fun h => hbF (hU h)
  have hVa : a ∉ V := fun h => haF (hV h)
  have hVb : b ∉ V := fun h => hbF (hV h)
  ext y
  have := congrArg (fun T => y ∈ T) h
  simp only [Finset.mem_insert] at this
  by_cases h1 : y = a
  · subst h1; simp [hUa, hVa]
  · by_cases h2 : y = b
    · subst h2; simp [hUb, hVb]
    · simpa [h1, h2] using this

theorem ps_dmu_eq {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ) (R R' : X → X → Prop)
    (b : X) (P : Finset X → Prop) [DecidablePred P]
    (hd : ∀ S x, x ∈ symmDiff (maxSet S R) (maxSet S R') ↔ x = b ∧ P S) :
    Dmu w R R' = (Finset.univ.filter P).card * w b := by
  unfold Dmu
  have : ∀ S : Finset X, symmDiff (maxSet S R) (maxSet S R') = if P S then {b} else ∅ := by
    intro S; ext x; rw [hd]; split_ifs with h <;> simp [h]
  simp only [this]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    Axiom3 (Dmu w) := by
  classical
  intro R a b hR hab
  have hrefl : ∀ x, ¬ asymmPart R x x := fun x h => h.2 (hR.1 x)
  have hD : Dmu w (prefAB a b) (prefABplus a b) = w b := (ps_eq8 w hw a b hab).2.2
  rw [hD]
  set F : Finset X := Finset.univ.filter (fun x => x ≠ a ∧ x ≠ b ∧ ¬ asymmPart R x b) with hF
  have haF : a ∉ F := by simp [hF]
  have hbF : b ∉ F := by simp [hF]
  constructor
  · intro hab' hba' _
    have hasym : ∀ y z, asymmPart (oplus R a b) y z ↔ asymmPart R y z ∨ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, oplus]
      simp only [asymmPart] at hab' hba'
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    let P : Finset X → Prop := fun S => a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, ¬ asymmPart R y b
    have hd : ∀ S x, x ∈ symmDiff (maxSet S R) (maxSet S (oplus R a b)) ↔ x = b ∧ P S := by
      intro S x
      simp only [Finset.mem_symmDiff, ps_mem_max, hasym, P]
      by_cases hxb : x = b
      · subst hxb
        constructor
        · rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
          · refine ⟨rfl, ?_, hx, h⟩
            by_contra haS
            apply hn
            refine ⟨hx, fun y hy hh => ?_⟩
            rcases hh with hh | ⟨rfl, _⟩
            · exact h y hy hh
            · exact haS hy
          · exact absurd ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩ hn
        · rintro ⟨-, ha, hb, h⟩
          left
          exact ⟨⟨hb, h⟩, fun hc => hc.2 a ha (Or.inr ⟨rfl, rfl⟩)⟩
      · simp only [hxb, false_and, iff_false]
        rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
        · apply hn; refine ⟨hx, fun y hy hh => ?_⟩
          try simp only [hxb, and_false, or_false] at hh
          exact h y hy hh
        · exact hn ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩
    rw [ps_dmu_eq w R (oplus R a b) b P hd]
    have hc : (Finset.univ.filter P).card = 2 ^ F.card := by
      apply ps_count a b F haF hbF
      intro S
      simp only [P, hF, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ha, hb, h⟩; exact ⟨ha, hb, fun y hy h1 h2 => ⟨h1, h2, h y hy⟩⟩
      · rintro ⟨ha, hb, h⟩
        refine ⟨ha, hb, fun y hy => ?_⟩
        by_cases h1 : y = a
        · subst h1; exact hab'
        · by_cases h2 : y = b
          · subst h2; exact hrefl _
          · exact (h y hy h1 h2).2.2
    have hN : Nb b R = F.card + 1 := by
      unfold Nb
      have : Finset.univ.filter (fun x => x ≠ b ∧ ¬ asymmPart R x b) = insert a F := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hF]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hxa : x = a
          · exact Or.inl hxa
          · exact Or.inr ⟨hxa, h1, h2⟩
        · rintro (rfl | ⟨_, h1, h2⟩)
          · exact ⟨hab, hab'⟩
          · exact ⟨h1, h2⟩
      convert (congrArg Finset.card this).trans (Finset.card_insert_of_notMem haF) using 2
      ext x; simp
    rw [hc, hN, Nat.add_sub_cancel]
    push_cast; ring
  · intro hab'
    have hasym : ∀ y z, asymmPart (ominus R a b) y z ↔ asymmPart R y z ∧ ¬ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, ominus]
      obtain ⟨hr1, hr2⟩ := hab'
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    let P : Finset X → Prop := fun S => a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, y ≠ a → ¬ asymmPart R y b
    have hd : ∀ S x, x ∈ symmDiff (maxSet S R) (maxSet S (ominus R a b)) ↔ x = b ∧ P S := by
      intro S x
      simp only [Finset.mem_symmDiff, ps_mem_max, hasym, P]
      by_cases hxb : x = b
      · subst hxb
        constructor
        · rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
          · exact absurd ⟨hx, fun y hy hh => h y hy hh.1⟩ hn
          · refine ⟨rfl, ?_, hx, fun y hy hya hh => h y hy ⟨hh, fun e => hya e.1⟩⟩
            by_contra haS
            apply hn
            refine ⟨hx, fun y hy hh => ?_⟩
            have hya : y ≠ a := by rintro rfl; exact haS hy
            exact h y hy ⟨hh, fun e => hya e.1⟩
        · rintro ⟨-, ha, hb, h⟩
          right
          refine ⟨⟨hb, fun y hy hh => h y hy (fun e => hh.2 ⟨e, rfl⟩) hh.1⟩, fun hc => ?_⟩
          exact hc.2 a ha hab'
      · simp only [hxb, false_and, iff_false]
        rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
        · exact hn ⟨hx, fun y hy hh => h y hy hh.1⟩
        · exact hn ⟨hx, fun y hy hh => h y hy ⟨hh, by simp⟩⟩
    rw [ps_dmu_eq w R (ominus R a b) b P hd]
    have hc : (Finset.univ.filter P).card = 2 ^ F.card := by
      apply ps_count a b F haF hbF
      intro S
      simp only [P, hF, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ha, hb, h⟩; exact ⟨ha, hb, fun y hy h1 h2 => ⟨h1, h2, h y hy h1⟩⟩
      · rintro ⟨ha, hb, h⟩
        refine ⟨ha, hb, fun y hy h1 => ?_⟩
        by_cases h2 : y = b
        · subst h2; exact hrefl _
        · exact (h y hy h1 h2).2.2
    have hN : Nb b R = F.card := by
      unfold Nb
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hF]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1, h2⟩
        rintro rfl; exact h2 hab'
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    rw [hc, hN]
    push_cast; ring
