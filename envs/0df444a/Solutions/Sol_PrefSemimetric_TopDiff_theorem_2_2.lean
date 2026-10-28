-- Prove2me | solution 1 for PrefSemimetric.TopDiff.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:15:57.899908+00:00
-- url     : https://prove2.me/submissions/54660f1f-7a8a-4886-ae35-d8769710d2d8

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

section
variable {X : Type*}

theorem ps_asymm_ominus (R : X → X → Prop) (a b : X) (h : asymmPart R a b) (x y : X) :
    asymmPart (ominus R a b) x y ↔ asymmPart R x y ∧ ¬ (x = a ∧ y = b) := by
  obtain ⟨h1, h2⟩ := h
  simp only [asymmPart, ominus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all

theorem ps_symm_ominus (R : X → X → Prop) (a b : X) (h : asymmPart R a b) (x y : X) :
    symmPart (ominus R a b) x y ↔ symmPart R x y := by
  obtain ⟨h1, h2⟩ := h
  simp only [symmPart, ominus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all

theorem ps_asymm_oplus (R : X → X → Prop) (a b : X) (hab : a ≠ b) (h1 : ¬ R a b) (h2 : ¬ R b a)
    (x y : X) : asymmPart (oplus R a b) x y ↔ asymmPart R x y ∨ (x = a ∧ y = b) := by
  simp only [asymmPart, oplus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all [eq_comm]

theorem ps_symm_oplus (R : X → X → Prop) (a b : X) (hab : a ≠ b) (h1 : ¬ R a b) (h2 : ¬ R b a)
    (x y : X) : symmPart (oplus R a b) x y ↔ symmPart R x y := by
  simp only [symmPart, oplus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all [eq_comm]

theorem ps_tg_add (S : X → X → Prop) (a b : X) {u v : X}
    (h : Relation.TransGen (fun x y => S x y ∨ (x = a ∧ y = b)) u v) :
    Relation.TransGen S u v ∨ (Relation.ReflTransGen S u a ∧ Relation.ReflTransGen S b v) := by
  induction h with
  | single h =>
    rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl (Relation.TransGen.single h)
    · exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ h ih =>
    rcases ih with ih | ⟨ih1, ih2⟩ <;> rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl (ih.tail h)
    · exact Or.inr ⟨ih.to_reflTransGen, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨ih1, ih2.tail h⟩
    · exact Or.inr ⟨ih1, Relation.ReflTransGen.refl⟩

theorem ps_path (R T : X → X → Prop) (x : X) : ∀ z, Relation.TransGen (asymmPart R) z x →
    Relation.TransGen (asymmPart T) z x ∨
      ∃ a v, asymmPart R a v ∧ ¬ asymmPart T a v ∧ Relation.ReflTransGen (asymmPart T) v x := by
  intro z h
  induction h using Relation.TransGen.head_induction_on with
  | @single z h =>
    by_cases hT : asymmPart T z x
    · exact Or.inl (Relation.TransGen.single hT)
    · exact Or.inr ⟨z, x, h, hT, Relation.ReflTransGen.refl⟩
  | @head z c h _ ih =>
    rcases ih with ih | ih
    · by_cases hT : asymmPart T z c
      · exact Or.inl (Relation.TransGen.head hT ih)
      · exact Or.inr ⟨z, c, h, hT, ih.to_reflTransGen⟩
    · exact Or.inr ih

theorem ps_step [Finite X] (R T : X → X → Prop) (hT : IsAcyclicOrder T)
    (hsymm : ∀ x y, symmPart R x y ↔ symmPart T x y)
    (hne : ∃ x y, ¬ (asymmPart R x y ↔ asymmPart T x y)) :
    (∃ a b, asymmPart R a b ∧ ¬ asymmPart T a b ∧ ∀ x, asymmPart T x b → asymmPart R x b) ∨
    (∃ a b, a ≠ b ∧ ¬ R a b ∧ ¬ R b a ∧ asymmPart T a b ∧
      ¬ Relation.ReflTransGen (asymmPart R) b a) := by
  classical
  by_cases hc : ∃ a b, asymmPart R a b ∧ ¬ asymmPart T a b ∧ ∀ x, asymmPart T x b → asymmPart R x b
  · exact Or.inl hc
  right
  push_neg at hc
  have hE : ∃ y b, asymmPart T y b ∧ ¬ asymmPart R y b := by
    obtain ⟨x, y, hxy⟩ := hne
    by_cases h1 : asymmPart R x y
    · have h2 : ¬ asymmPart T x y := fun h => hxy ⟨fun _ => h, fun _ => h1⟩
      obtain ⟨z, hz⟩ := hc x y h1 h2
      exact ⟨z, y, hz⟩
    · have h2 : asymmPart T x y := by
        by_contra h2; exact hxy ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      exact ⟨x, y, h2, h1⟩
  let r : X → X → Prop := fun b' b => Relation.TransGen (asymmPart T) b' b
  have hwf : WellFounded r := by
    haveI : IsTrans X r := ⟨fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2⟩
    haveI : IsIrrefl X r := ⟨fun x => hT.2 x⟩
    exact Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨y0, b0, hy0⟩ := hE
  obtain ⟨b, ⟨x, hxb⟩, hmin⟩ := hwf.has_min {b | ∃ y, asymmPart T y b ∧ ¬ asymmPart R y b}
    ⟨b0, y0, hy0⟩
  have hxb' : x ≠ b := fun h => by subst h; exact hxb.1.2 hxb.1.1
  have hnp : ¬ Relation.TransGen (asymmPart R) b x := by
    intro hp
    rcases ps_path R T x b hp with h | ⟨a, v, h1, h2, h3⟩
    · exact hT.2 b (h.tail hxb.1)
    · obtain ⟨y, hy⟩ := hc a v h1 h2
      exact hmin v ⟨y, hy⟩ (Relation.TransGen.tail' h3 hxb.1)
  refine ⟨x, b, hxb', ?_, ?_, hxb.1, ?_⟩
  · intro h
    have : R b x := by by_contra hh; exact hxb.2 ⟨h, hh⟩
    exact hxb.1.2 ((hsymm x b).1 ⟨h, this⟩).2
  · intro h
    by_cases hh : R x b
    · exact hxb.1.2 ((hsymm x b).1 ⟨hh, h⟩).2
    · exact hnp (Relation.TransGen.single ⟨h, hh⟩)
  · intro h
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with h | h
    · exact hxb' h
    · exact hnp h

open Classical in
noncomputable def psM [Fintype X] (P T : X → X → Prop) : ℕ :=
  (Finset.univ.filter (fun p : X × X => ¬ (asymmPart P p.1 p.2 ↔ asymmPart T p.1 p.2))).card

theorem ps_m_lt [Fintype X] (P R0 T : X → X → Prop) (a b : X)
    (hout : ∀ x y, ¬ (x = a ∧ y = b) → (asymmPart R0 x y ↔ asymmPart P x y))
    (hin : ¬ (asymmPart P a b ↔ asymmPart T a b)) (hin0 : (asymmPart R0 a b ↔ asymmPart T a b)) :
    psM R0 T < psM P T := by
  classical
  unfold psM
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨(a, b), by simpa using hin, by simpa using hin0⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    by_cases hq : p.1 = a ∧ p.2 = b
    · rw [hq.1, hq.2]; exact hin
    · rwa [← hout p.1 p.2 hq]
end

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (R T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T) (hne : R ≠ T)
    (hsymm : ∀ x y, symmPart R x y ↔ symmPart T x y) :
    InBetween R T T := by
  classical
  suffices H : ∀ n, ∀ P, psM P T = n → IsAcyclicOrder P → P ≠ T →
      (∀ x y, symmPart P x y ↔ symmPart T x y) → InBetween P T T from
    H _ R rfl hR hne hsymm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hm hP hPT hPs
  have hd : ∃ x y, ¬ (asymmPart P x y ↔ asymmPart T x y) := by
    by_contra hc
    push_neg at hc
    apply hPT
    funext x y
    apply propext
    have e1 := hc x y
    have e2 := hPs x y
    have e3 := hc y x
    simp only [asymmPart, symmPart] at e1 e2 e3
    by_cases p1 : P x y <;> by_cases p2 : P y x <;> by_cases t1 : T x y <;> by_cases t2 : T y x <;>
      simp_all
  have key : ∃ R0, OneStepToward P R0 T ∧ psM R0 T < psM P T ∧
      ∀ x y, symmPart R0 x y ↔ symmPart T x y := by
    rcases ps_step P T hT hPs hd with ⟨a, b, h1, h2, h3⟩ | ⟨a, b, hab, h1, h2, h3, h4⟩
    · have hab : a ≠ b := by rintro rfl; exact h1.2 h1.1
      refine ⟨ominus P a b, ⟨⟨fun x => ⟨hP.1 x, fun h => hab (h.1.symm.trans h.2)⟩,
        fun x hx => hP.2 x (Relation.TransGen.mono
          (fun u v h => ((ps_asymm_ominus P a b h1 u v).1 h).1) _ _ hx)⟩,
        Or.inl ⟨a, b, h1, rfl, h2, h3⟩⟩, ?_, ?_⟩
      · apply ps_m_lt P _ T a b
        · intro x y hq
          rw [ps_asymm_ominus P a b h1]
          simp only [hq, not_false_eq_true, and_true]
        · exact fun h => h2 (h.1 h1)
        · exact ⟨fun h => absurd ⟨rfl, rfl⟩ ((ps_asymm_ominus P a b h1 a b).1 h).2,
            fun h => absurd h h2⟩
      · intro x y
        exact (ps_symm_ominus P a b h1 x y).trans (hPs x y)
    · refine ⟨oplus P a b, ⟨⟨fun x => ⟨Or.inl (hP.1 x), fun h => hab (h.2.symm.trans h.1)⟩,
        fun z hz => ?_⟩, Or.inr ⟨a, b, fun h => h1 h.1, fun h => h2 h.1, rfl, h3⟩⟩, ?_, ?_⟩
      · have hz' := Relation.TransGen.mono
          (p := fun x y => asymmPart P x y ∨ (x = a ∧ y = b))
          (fun u v h => (ps_asymm_oplus P a b hab h1 h2 u v).1 h) _ _ hz
        rcases ps_tg_add (asymmPart P) a b hz' with h | ⟨h5, h6⟩
        · exact hP.2 z h
        · exact h4 (h6.trans h5)
      · apply ps_m_lt P _ T a b
        · intro x y hq
          rw [ps_asymm_oplus P a b hab h1 h2]
          simp only [hq, or_false]
        · exact fun h => h1 (h.2 h3).1
        · exact ⟨fun _ => h3, fun _ => (ps_asymm_oplus P a b hab h1 h2 a b).2 (Or.inr ⟨rfl, rfl⟩)⟩
      · intro x y
        exact (ps_symm_oplus P a b hab h1 h2 x y).trans (hPs x y)
  obtain ⟨R0, hstep, hlt, hs0⟩ := key
  by_cases h0 : R0 = T
  · rw [h0] at hstep
    exact Relation.TransGen.single hstep
  · exact Relation.TransGen.head hstep (ih _ (hm ▸ hlt) R0 rfl hstep.1 h0 hs0)
