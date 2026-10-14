-- Prove2me | solution 1 for StrategyProofArrow.Dictatorship.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:04:16.932435+00:00
-- url     : https://prove2.me/submissions/dbd1b849-f065-4b69-b1d4-4dd046ab0a04

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic



namespace StrategyProofArrow.Dictatorship

open AGT

theorem dsto_tri {A : Type*} {r : A → A → Prop} (h : IsStrictTotalOrder A r) (x y : A) :
    r x y ∨ x = y ∨ r y x := by
  by_cases h1 : r x y
  · exact Or.inl h1
  by_cases h2 : r y x
  · exact Or.inr (Or.inr h2)
  exact Or.inr (Or.inl (h.toTrichotomous.trichotomous x y h1 h2))

theorem dsto_irr {A : Type*} {r : A → A → Prop} (h : IsStrictTotalOrder A r) (x : A) :
    ¬ r x x := h.toIsStrictOrder.toIrrefl.irrefl x

theorem dsto_trans {A : Type*} {r : A → A → Prop} (h : IsStrictTotalOrder A r) {x y z : A}
    (h1 : r x y) (h2 : r y z) : r x z := h.toIsStrictOrder.toIsTrans.trans x y z h1 h2

theorem dsto_asymm {A : Type*} {r : A → A → Prop} (h : IsStrictTotalOrder A r) {x y : A}
    (h1 : r x y) (h2 : r y x) : False := dsto_irr h x (dsto_trans h h1 h2)

theorem dsto_mk {A : Type*} {r : A → A → Prop}
    (tri : ∀ a b, ¬ r a b → ¬ r b a → a = b) (irr : ∀ a, ¬ r a a)
    (trans : ∀ a b c, r a b → r b c → r a c) : IsStrictTotalOrder A r :=
  @IsStrictTotalOrder.mk _ _ ⟨tri⟩ (@IsStrictOrder.mk _ _ ⟨irr⟩ ⟨trans⟩)

/-- hybrid profile -/
def dhyb {ι A : Type*} [DecidableEq ι] (C D : ι → A → A → Prop) (S : Finset ι) :
    ι → A → A → Prop := fun i => if i ∈ S then D i else C i

theorem dhyb_pref {ι A : Type*} [DecidableEq ι] {C D : ι → A → A → Prop}
    (hC : IsPrefProfile C) (hD : IsPrefProfile D) (S : Finset ι) :
    IsPrefProfile (dhyb C D S) := by
  intro i; unfold dhyb; split_ifs
  · exact hD i
  · exact hC i

theorem dhyb_empty {ι A : Type*} [DecidableEq ι] (C D : ι → A → A → Prop) :
    dhyb C D ∅ = C := by funext i; simp [dhyb]

theorem dhyb_univ {ι A : Type*} [Fintype ι] [DecidableEq ι] (C D : ι → A → A → Prop) :
    dhyb C D Finset.univ = D := by funext i; simp [dhyb]

theorem dhyb_insert {ι A : Type*} [DecidableEq ι] (C D : ι → A → A → Prop) (S : Finset ι)
    (a : ι) : dhyb C D (insert a S) = Function.update (dhyb C D S) a (D a) := by
  funext i
  by_cases h : i = a
  · subst h; simp [dhyb]
  · simp [dhyb, Function.update_of_ne h, h]

theorem dhyb_back {ι A : Type*} [DecidableEq ι] (C D : ι → A → A → Prop) (S : Finset ι)
    (a : ι) (ha : a ∉ S) :
    Function.update (Function.update (dhyb C D S) a (D a)) a (C a) = dhyb C D S := by
  rw [Function.update_idem]
  have : C a = dhyb C D S a := by simp [dhyb, ha]
  rw [this, Function.update_eq_self]

theorem dmem_range {ι A : Type*} (f : (ι → A → A → Prop) → A) {P : ι → A → A → Prop}
    (hP : IsPrefProfile P) : f P ∈ range f := ⟨P, hP, rfl⟩

theorem dupdate_pref {ι A : Type*} [DecidableEq ι] {P : ι → A → A → Prop}
    (hP : IsPrefProfile P) (i : ι) {r : A → A → Prop} (hr : IsStrictTotalOrder A r) :
    IsPrefProfile (Function.update P i r) := by
  intro j
  by_cases h : j = i
  · subst h; simp [hr]
  · rw [Function.update_of_ne h]; exact hP j

/-- Lemma 6 for any number of voters. -/
theorem lemma_6_core {ι A : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f)
    (C D : ι → A → A → Prop) (hC : IsPrefProfile C) (hD : IsPrefProfile D)
    (hCD : ∀ i, AgreeOn (range f) (C i) (D i)) :
    f C = f D := by
  have key : ∀ S : Finset ι, f (dhyb C D S) = f C := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [dhyb_empty]
    | insert a S ha ih =>
      rw [← ih, dhyb_insert]
      have hM := dhyb_pref hC hD S
      have hMa : dhyb C D S a = C a := by simp [dhyb, ha]
      set u := f (dhyb C D S) with hu
      set v := f (Function.update (dhyb C D S) a (D a)) with hv
      have h1 := hsp _ hM a (D a) (hD a)
      rw [hMa] at h1
      have hM' := dupdate_pref hM a (hD a)
      have h2 := hsp _ hM' a (C a) (hC a)
      rw [dhyb_back C D S a ha] at h2
      simp only [Function.update_self] at h2
      by_contra hne
      rcases dsto_tri (hC a) u v with h | h | h
      · exact h2 ((hCD a u (dmem_range f hM) v (dmem_range f hM')).1 h)
      · exact hne h.symm
      · exact h1 h
  have := key Finset.univ
  rw [dhyb_univ] at this
  exact this.symm

/-- Lemma 1 (Condition U) for any nonempty set of voters. -/
theorem lemma_1_core {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f) : ConditionU f := by
  intro P hP x hx
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨Q, hQ, hQx⟩ := (hx i0).1
  have key : ∀ S : Finset ι, f (dhyb Q P S) = x := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [dhyb_empty, hQx]
    | insert a S ha ih =>
      rw [dhyb_insert]
      have hM := dhyb_pref hQ hP S
      have hM' := dupdate_pref hM a (hP a)
      have h2 := hsp _ hM' a (Q a) (hQ a)
      rw [dhyb_back Q P S a ha, ih] at h2
      simp only [Function.update_self] at h2
      by_contra hne
      exact h2 ((hx a).2 _ (dmem_range f hM') hne)
  have := key Finset.univ
  rwa [dhyb_univ] at this

theorem dict_condU {ι A : Type*} (f : (ι → A → A → Prop) → A) (hd : Dictatorial f) :
    ConditionU f := by
  obtain ⟨i, hi⟩ := hd
  intro P hP x hx
  by_contra hne
  exact dsto_asymm (hP i) ((hi P hP).2 x (hx i).1 (Ne.symm hne)) ((hx i).2 _ (hi P hP).1 hne)

theorem one_voter_dict {ι A : Type*} [DecidableEq ι] (i0 : ι) (hall : ∀ j : ι, j = i0)
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f) : Dictatorial f := by
  refine ⟨i0, fun P hP => ⟨dmem_range f hP, fun y hy hne => ?_⟩⟩
  obtain ⟨Q, hQ, rfl⟩ := hy
  have hup : Function.update P i0 (Q i0) = Q := by
    funext j; rw [hall j]; simp
  have h := hsp P hP i0 (Q i0) (hQ i0)
  rw [hup] at h
  rcases dsto_tri (hP i0) (f P) (f Q) with h1 | h1 | h1
  · exact h1
  · exact absurd h1.symm hne
  · exact absurd h1 h

theorem lemma_2_core {ι A : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Fintype.card ι = 1)
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f := by
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 hn
  have hd := one_voter_dict i0 hi0 f hsp
  by_cases hr : range f = Set.univ
  · exact Or.inl ⟨hr, hd⟩
  · right
    refine ⟨?_, dict_condU f hd⟩
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 hr
    exact ⟨x, fun P hP h => hx (h ▸ dmem_range f hP)⟩

theorem delim_update {ι A : Type*} [DecidableEq ι] (b : A → A → Prop)
    (Q : ι → A → A → Prop) (i : ι) (r : A → A → Prop) :
    (fun o : Option ι => o.elim b (Function.update Q i r)) =
      Function.update (fun o : Option ι => o.elim b Q) (some i) r := by
  funext o
  cases o with
  | none => simp
  | some j =>
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h, h]

theorem lemma_3_core {ι A : Type*} [DecidableEq ι]
    (f : (Option ι → A → A → Prop) → A) :
    (∀ P : Option ι → A → A → Prop, IsPrefProfile P →
        ∀ (i : ι) (r' : A → A → Prop), IsStrictTotalOrder A r' →
          ¬ P (some i) (f (Function.update P (some i) r')) (f P)) ↔
      ∀ b : A → A → Prop, IsStrictTotalOrder A b → IncentiveCompatible (sectionAt f b) := by
  constructor
  · intro H b hb Q hQ i r' hr'
    have hP : IsPrefProfile (fun o : Option ι => o.elim b Q) := by
      intro o; cases o with
      | none => exact hb
      | some j => exact hQ j
    have h := H _ hP i r' hr'
    simp only [sectionAt]
    rw [delim_update]
    exact h
  · intro H P hP i r' hr'
    have hPe : (fun o : Option ι => o.elim (P none) (fun j => P (some j))) = P := by
      funext o; cases o <;> rfl
    have h := H (P none) (hP none) (fun j => P (some j)) (fun j => hP (some j)) i r' hr'
    simp only [sectionAt] at h
    rw [delim_update, hPe] at h
    exact h

open Classical in
/-- extend a relation on `T` to `A` -/
noncomputable def dext {A : Type*} [Fintype A] (T : Set A) (q : T → T → Prop) :
    A → A → Prop :=
  fun x y =>
    if hx : x ∈ T then (if hy : y ∈ T then q ⟨x, hx⟩ ⟨y, hy⟩ else True)
    else (if y ∈ T then False else Fintype.equivFin A x < Fintype.equivFin A y)

theorem dext_mem {A : Type*} [Fintype A] (T : Set A) (q : T → T → Prop) {x y : A}
    (hx : x ∈ T) (hy : y ∈ T) : dext T q x y ↔ q ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [dext, hx, hy]

theorem dext_sto {A : Type*} [Fintype A] (T : Set A) (q : T → T → Prop)
    (hq : IsStrictTotalOrder T q) : IsStrictTotalOrder A (dext T q) := by
  apply dsto_mk
  · intro a b h1 h2
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> simp [dext, ha, hb] at h1 h2
    · rcases dsto_tri hq ⟨a, ha⟩ ⟨b, hb⟩ with h | h | h
      · exact absurd h h1
      · exact congrArg Subtype.val h
      · exact absurd h h2
    · exact (Fintype.equivFin A).injective (Fin.ext (le_antisymm h2 h1))
  · intro a
    by_cases ha : a ∈ T <;> simp [dext, ha]
    exact dsto_irr hq _
  · intro a b c h1 h2
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> by_cases hc : c ∈ T <;>
      simp [dext, ha, hb, hc] at h1 h2 ⊢
    · exact dsto_trans hq h1 h2
    · exact lt_trans h1 h2

theorem restrict_sto {A : Type*} (T : Set A) {r : A → A → Prop}
    (hr : IsStrictTotalOrder A r) : IsStrictTotalOrder T (fun x y : T => r x y) := by
  apply dsto_mk
  · intro a b h1 h2
    rcases dsto_tri hr a b with h | h | h
    · exact absurd h h1
    · exact Subtype.ext h
    · exact absurd h h2
  · intro a; exact dsto_irr hr _
  · intro a b c h1 h2; exact dsto_trans hr h1 h2

theorem restriction_factor_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f)
    (hne : (range f).Nonempty) :
    ∃ g : (ι → range f → range f → Prop) → range f,
      (∀ P : ι → A → A → Prop, IsPrefProfile P →
        ((g (fun i (x y : range f) => P i x y) : A) = f P)) ∧
      IncentiveCompatible g := by
  classical
  set T := range f with hT
  obtain ⟨x0, hx0⟩ := hne
  let g : (ι → T → T → Prop) → T := fun Q =>
    if h : IsPrefProfile Q then
      ⟨f (fun i => dext T (Q i)), dmem_range f (fun i => dext_sto T (Q i) (h i))⟩
    else ⟨x0, hx0⟩
  have hg : ∀ Q (h : IsPrefProfile Q), g Q =
      ⟨f (fun i => dext T (Q i)), dmem_range f (fun i => dext_sto T (Q i) (h i))⟩ := by
    intro Q h; simp only [g, dif_pos h]
  refine ⟨g, ?_, ?_⟩
  · intro P hP
    have hQ : IsPrefProfile (fun i (x y : T) => P i x y) := fun i => restrict_sto T (hP i)
    rw [hg _ hQ]
    apply lemma_6_core f hsp _ _ (fun i => dext_sto T _ (hQ i)) hP
    intro i x hx y hy
    rw [dext_mem T _ hx hy]
  · intro Q hQ i r' hr'
    have hQ' := dupdate_pref hQ i hr'
    rw [hg _ hQ, hg _ hQ']
    have hfun : (fun j => dext T (Function.update Q i r' j)) =
        Function.update (fun j => dext T (Q j)) i (dext T r') := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    have hP : IsPrefProfile (fun j => dext T (Q j)) := fun j => dext_sto T _ (hQ j)
    have h := hsp _ hP i (dext T r') (dext_sto T _ hr')
    rw [← hfun] at h
    intro hc
    apply h
    rw [dext_mem T _ (dmem_range f (fun j => dext_sto T _ (hQ' j))) (dmem_range f hP)]
    exact hc

theorem lemma_1_main {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    ConditionU f := by
  haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  exact lemma_1_core f hsp

theorem lemma_6_main {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f)
    (C D : ι → A → A → Prop) (hC : IsPrefProfile C) (hD : IsPrefProfile D)
    (hCD : ∀ i, AgreeOn (range f) (C i) (D i)) :
    f C = f D := lemma_6_core f hsp C D hC hD hCD

theorem restriction_factor_main {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι)
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f)
    (hstrong : StrongAltExcluding f)
    (hp : 3 ≤ (range f).ncard)
    (hproper : (range f).ncard < Fintype.card A) :
    ∃ g : (ι → range f → range f → Prop) → range f,
      (∀ P : ι → A → A → Prop, IsPrefProfile P →
        ((g (fun i (x y : range f) => P i x y) : A) = f P)) ∧
      IncentiveCompatible g :=
  restriction_factor_core f hsp (Set.nonempty_of_ncard_ne_zero (by omega))

end StrategyProofArrow.Dictatorship

open StrategyProofArrow.Dictatorship
open AGT

theorem solution {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : Fintype.card A = 3)
    (f : (Option ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard) :
    (∀ P : Option ι → A → A → Prop, IsPrefProfile P →
        ∀ (i : ι) (r' : A → A → Prop), IsStrictTotalOrder A r' →
          ¬ P (some i) (f (Function.update P (some i) r')) (f P)) ↔
      ∀ b : A → A → Prop, IsStrictTotalOrder A b → IncentiveCompatible (sectionAt f b) := by
  exact lemma_3_core f
