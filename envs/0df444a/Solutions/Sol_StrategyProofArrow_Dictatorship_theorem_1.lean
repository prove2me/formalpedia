-- Prove2me | solution 1 for StrategyProofArrow.Dictatorship.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:06:51.446096+00:00
-- url     : https://prove2.me/submissions/5168fd3a-e933-4a5a-836a-b3a2e26f879a

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic
import Definitions.Def_StrategyProofArrow_WeakGS_Basic



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


section GSCore
open StrategyProofArrow.WeakGS

def g4lift {A : Type*} (a : A) (R : StrategyProofArrow.Correspondence.StrongOrder A) :
    StrategyProofArrow.Correspondence.StrongOrder A :=
  ⟨{ rel := fun u w => u = a ∨ (w ≠ a ∧ R.1.rel u w)
     total := by
       intro u w
       by_cases hu : u = a
       · exact Or.inl (Or.inl hu)
       · by_cases hw : w = a
         · exact Or.inr (Or.inl hw)
         · rcases R.1.total u w with h | h
           · exact Or.inl (Or.inr ⟨hw, h⟩)
           · exact Or.inr (Or.inr ⟨hu, h⟩)
     trans := by
       rintro u w t (hu | ⟨hw, huw⟩) (hw' | ⟨ht, hwt⟩)
       · exact Or.inl hu
       · exact Or.inl hu
       · exact absurd hw' hw
       · exact Or.inr ⟨ht, R.1.trans _ _ _ huw hwt⟩ },
   by
     rintro u w (hu | ⟨hw, huw⟩) (hw' | ⟨hu', hwu⟩)
     · rw [hu, hw']
     · exact absurd hu hu'
     · exact absurd hw' hw
     · exact R.2 _ _ huw hwu⟩

@[simp] theorem g4lift_rel {A : Type*} (a : A) (R : StrategyProofArrow.Correspondence.StrongOrder A)
    (u w : A) : (g4lift a R).1.rel u w ↔ (u = a ∨ (w ≠ a ∧ R.1.rel u w)) := Iff.rfl

noncomputable def g4Q0 (A : Type*) [Fintype A] : StrategyProofArrow.Correspondence.StrongOrder A :=
  ⟨{ rel := fun u w => ((Fintype.equivFin A) u : ℕ) ≤ (Fintype.equivFin A) w
     total := fun _ _ => le_total _ _
     trans := fun _ _ _ => le_trans },
   fun _ _ h1 h2 => (Fintype.equivFin A).injective (Fin.ext (le_antisymm h1 h2))⟩

noncomputable def g4top2 {A : Type*} [Fintype A] (x y : A) : StrategyProofArrow.Correspondence.StrongOrder A :=
  g4lift x (g4lift y (g4Q0 A))

noncomputable def g4top3 {A : Type*} [Fintype A] (x y z : A) :
    StrategyProofArrow.Correspondence.StrongOrder A :=
  g4lift x (g4lift y (g4lift z (g4Q0 A)))

noncomputable def g4T2 {ι A : Type*} [Fintype A] [DecidableEq ι] (x y : A) (S : Finset ι) :
    StrategyProofArrow.Correspondence.StrongProfile ι A :=
  fun i => if i ∈ S then g4top2 x y else g4top2 y x

theorem g4_strong_rel_iff' {A : Type*} (S : StrategyProofArrow.Correspondence.StrongOrder A) {x y : A}
    (hxy : x ≠ y) : S.1.rel x y ↔ ¬ S.1.rel y x := by
  constructor
  · intro h h'; exact hxy (S.2 x y h h')
  · intro h; exact (S.1.total x y).resolve_right h

section
set_option linter.unusedSectionVars false
variable {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]

theorem g4_mono_step (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (P : StrategyProofArrow.Correspondence.StrongProfile ι A) (i : ι)
    (c : StrategyProofArrow.Correspondence.StrongOrder A)
    (h : ∀ z, (P i).1.rel (ν P) z → c.1.rel (ν P) z) : ν (Function.update P i c) = ν P := by
  have h1 := hν P i c
  have h2 := hν (Function.update P i c) i (P i)
  simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at h2
  by_contra hne
  have hca : ¬ c.1.rel (ν P) (ν (Function.update P i c)) := by
    intro hc
    exact h2 ⟨hc, fun hc' => hne (c.2 _ _ hc' hc)⟩
  have hPa : ¬ (P i).1.rel (ν P) (ν (Function.update P i c)) := fun hp => hca (h _ hp)
  exact h1 ⟨((P i).1.total _ _).resolve_right hPa, hPa⟩

theorem g4_mono (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (C C' : StrategyProofArrow.Correspondence.StrongProfile ι A)
    (h : ∀ i z, (C i).1.rel (ν C) z → (C' i).1.rel (ν C) z) : ν C' = ν C := by
  let D : Finset ι → StrategyProofArrow.Correspondence.StrongProfile ι A := fun S j =>
    if j ∈ S then C' j else C j
  have key : ∀ S : Finset ι, ν (D S) = ν C := by
    intro S
    induction S using Finset.induction_on with
    | empty => congr 1
    | insert i S hi ih =>
      have hDi : D S i = C i := by simp [D, hi]
      have hstep := g4_mono_step ν hν (D S) i (C' i) (by
        intro z hz
        rw [hDi, ih] at hz
        rw [ih]
        exact h i z hz)
      rw [← ih, ← hstep]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [D]
      · simp [D, hj]
  have := key Finset.univ
  rw [← this]
  congr 1
  funext j
  simp [D]

theorem g4_unan (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (a w : A)
    (ha : a ∈ Set.range ν) (haw : a ≠ w) (h : ∀ i, (C i).1.strict a w) : ν C ≠ w := by
  obtain ⟨D, hD⟩ := ha
  intro hw
  let E : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i => g4lift a (C i)
  have e1 : ν E = ν C := g4_mono ν hν C E (by
    intro i z hz
    rw [hw] at hz ⊢
    show (g4lift a (C i)).1.rel w z
    rw [g4lift_rel]
    refine Or.inr ⟨?_, hz⟩
    rintro rfl
    exact (h i).2 hz)
  have e2 : ν E = ν D := g4_mono ν hν D E (by
    intro i z _
    rw [hD]
    show (g4lift a (C i)).1.rel a z
    rw [g4lift_rel]
    exact Or.inl rfl)
  apply haw
  rw [← hD, ← e2, e1, hw]

theorem g4_in2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y : A)
    (hxR : x ∈ Set.range ν)
    (h : ∀ w, w ≠ x → w ≠ y → ∀ i, (C i).1.strict x w) : ν C = x ∨ ν C = y := by
  by_contra hc
  push_neg at hc
  exact g4_unan ν hν C x (ν C) hxR (Ne.symm hc.1) (h _ hc.1 hc.2) rfl

theorem g4_in3 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y z : A)
    (hxR : x ∈ Set.range ν)
    (h : ∀ w, w ≠ x → w ≠ y → w ≠ z → ∀ i, (C i).1.strict x w) :
    ν C = x ∨ ν C = y ∨ ν C = z := by
  by_contra hc
  push_neg at hc
  exact g4_unan ν hν C x (ν C) hxR (Ne.symm hc.1) (h _ hc.1 hc.2.1 hc.2.2) rfl

def g4D (ν : StrictVotingProcedure ι A) (x y : A) (S : Finset ι) : Prop := ν (g4T2 x y S) = x

theorem g4T2_compl (x y : A) (S : Finset ι) : g4T2 x y S = g4T2 y x Sᶜ := by
  funext i
  by_cases hi : i ∈ S <;> simp [g4T2, hi]

theorem g4T2_in2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (S : Finset ι) :
    ν (g4T2 x y S) = x ∨ ν (g4T2 x y S) = y := by
  apply g4_in2 ν hν _ x y hxR
  intro w hwx hwy i
  by_cases hi : i ∈ S <;>
    simp [g4T2, hi, g4top2, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hxy,
      Ne.symm hwx, Ne.symm hwy, Ne.symm hxy]

theorem g4D_compl (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (S : Finset ι) :
    g4D ν x y S ↔ ¬ g4D ν y x Sᶜ := by
  unfold g4D
  rw [← g4T2_compl]
  rcases g4T2_in2 ν hν x y hxy hxR S with h | h <;> rw [h]
  · simp [hxy]
  · simp [Ne.symm hxy]

theorem g4D_univ (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) : g4D ν x y Finset.univ := by
  unfold g4D
  rcases g4T2_in2 ν hν x y hxy hxR Finset.univ with h | h
  · exact h
  · exfalso
    apply g4_unan ν hν _ x y hxR hxy _ h
    intro i
    simp [g4T2, g4top2, StrategyProofArrow.Correspondence.WeakOrder.strict, hxy, Ne.symm hxy]

theorem g4D_empty (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) : ¬ g4D ν x y ∅ := by
  rw [g4D_compl ν hν x y hxy hxR]
  simp only [Finset.compl_empty, not_not]
  exact g4D_univ ν hν y x (Ne.symm hxy) hyR

theorem g4D_mono (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (S T : Finset ι) (hST : S ⊆ T) (h : g4D ν x y S) : g4D ν x y T := by
  unfold g4D at *
  rw [← h]
  apply g4_mono ν hν
  intro i z hz
  rw [h] at hz ⊢
  by_cases hiT : i ∈ T
  · simp [g4T2, hiT, g4top2]
  · have hiS : i ∉ S := fun hs => hiT (hST hs)
    simpa [g4T2, hiT, hiS] using hz

theorem g4_key2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y : A) (hx : ν C = x)
    (S : Finset ι) (hS : ∀ i, i ∈ S ↔ (C i).1.rel x y) : g4D ν x y S := by
  unfold g4D
  rw [← hx]
  apply g4_mono ν hν
  intro i z hz
  rw [hx] at hz ⊢
  by_cases hi : i ∈ S
  · simp [g4T2, hi, g4top2]
  · have hn : ¬ (C i).1.rel x y := fun h => hi ((hS i).2 h)
    have hzy : z ≠ y := by rintro rfl; exact hn hz
    simp [g4T2, hi, g4top2, hzy]

theorem g4_rule1 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) (hzR : z ∈ Set.range ν)
    (S : Finset ι) (h : g4D ν x y S) : g4D ν x z S := by
  let C : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i =>
    if i ∈ S then g4top3 x y z else g4top3 y z x
  have ho := g4_in3 ν hν C x y z hxR (by
    intro w hwx hwy hwz i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hwz,
        hxy, hxz, hyz, Ne.symm hwx, Ne.symm hwy, Ne.symm hwz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
  rcases ho with ho | ho | ho
  · apply g4_key2 ν hν C x z ho S
    intro i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  · exfalso
    have := g4_key2 ν hν C y x ho Sᶜ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact (g4D_compl ν hν x y hxy hxR S).1 h this
  · exfalso
    have := g4_key2 ν hν C z y ho ∅ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact g4D_empty ν hν z y (Ne.symm hyz) hzR hyR this

theorem g4_rule2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) (hzR : z ∈ Set.range ν)
    (S : Finset ι) (h : g4D ν x y S) : g4D ν z y S := by
  let C : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i =>
    if i ∈ S then g4top3 z x y else g4top3 y z x
  have ho := g4_in3 ν hν C x y z hxR (by
    intro w hwx hwy hwz i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hwz,
        hxy, hxz, hyz, Ne.symm hwx, Ne.symm hwy, Ne.symm hwz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
  rcases ho with ho | ho | ho
  · exfalso
    have := g4_key2 ν hν C x z ho ∅ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact g4D_empty ν hν x z hxz hxR hzR this
  · exfalso
    have := g4_key2 ν hν C y x ho Sᶜ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact (g4D_compl ν hν x y hxy hxR S).1 h this
  · apply g4_key2 ν hν C z y ho S
    intro i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]


theorem g4_third (ν : StrictVotingProcedure ι A) (hR : 3 ≤ (Set.range ν).ncard) (x y : A) :
    ∃ z ∈ Set.range ν, z ≠ x ∧ z ≠ y := by
  by_contra hc
  push_neg at hc
  have hsub : Set.range ν ⊆ ({x, y} : Set A) := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    · simp [hc z hz hzx]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set A).ncard ≤ 2 := by
    calc ({x, y} : Set A).ncard ≤ ({y} : Set A).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  omega

def g4Dec (ν : StrictVotingProcedure ι A) (S : Finset ι) : Prop :=
  ∀ u ∈ Set.range ν, ∀ v ∈ Set.range ν, u ≠ v → g4D ν u v S

theorem g4_expand (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (hR : 3 ≤ (Set.range ν).ncard) (x y : A) (hxy : x ≠ y)
    (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) (S : Finset ι) (h : g4D ν x y S) :
    g4Dec ν S := by
  have h1 : ∀ v ∈ Set.range ν, v ≠ x → g4D ν x v S := by
    intro v hvR hvx
    by_cases hvy : v = y
    · rw [hvy]; exact h
    · exact g4_rule1 ν hν x y v hxy (Ne.symm hvx) (Ne.symm hvy) hxR hyR hvR S h
  intro u huR v hvR huv
  by_cases hux : u = x
  · rw [hux] at huv ⊢; exact h1 v hvR (Ne.symm huv)
  · by_cases hvx : v = x
    · obtain ⟨w, hwR, hwu, hwx⟩ := g4_third ν hR u x
      have a1 := h1 w hwR hwx
      have a2 := g4_rule2 ν hν x w u (Ne.symm hwx) (Ne.symm hux) hwu hxR hwR huR S a1
      rw [hvx]
      exact g4_rule1 ν hν u w x (Ne.symm hwu) hux hwx huR hwR hxR S a2
    · have a1 := h1 v hvR hvx
      exact g4_rule2 ν hν x v u (Ne.symm hvx) (Ne.symm hux) (Ne.symm huv) hxR hvR huR S a1

theorem g4_contract (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (hR : 3 ≤ (Set.range ν).ncard) (S1 S2 : Finset ι) (hdisj : Disjoint S1 S2)
    (h : g4Dec ν (S1 ∪ S2)) : g4Dec ν S1 ∨ g4Dec ν S2 := by
  have hne : (Set.range ν).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x, hxR⟩ := hne
  obtain ⟨y, hyR, hyx, -⟩ := g4_third ν hR x x
  obtain ⟨z, hzR, hzx, hzy⟩ := g4_third ν hR x y
  have hxy : x ≠ y := Ne.symm hyx
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  let C : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i =>
    if i ∈ S1 then g4top3 x y z else if i ∈ S2 then g4top3 z x y else g4top3 y z x
  have hd := h x hxR y hyR hxy
  have ho := g4_in3 ν hν C x y z hxR (by
    intro w hwx hwy hwz i
    by_cases hi : i ∈ S1 <;> by_cases hi2 : i ∈ S2 <;>
      simp [C, hi, hi2, g4top3, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hwz,
        hxy, hxz, hyz, Ne.symm hwx, Ne.symm hwy, Ne.symm hwz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
  have hdis : ∀ i, i ∈ S1 → i ∉ S2 := fun i h1 h2 => Finset.disjoint_left.1 hdisj h1 h2
  rcases ho with ho | ho | ho
  · left
    apply g4_expand ν hν hR x z hxz hxR hzR S1
    apply g4_key2 ν hν C x z ho S1
    intro i
    by_cases hi : i ∈ S1
    · simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
    · by_cases hi2 : i ∈ S2 <;>
        simp [C, hi, hi2, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  · exfalso
    have := g4_key2 ν hν C y x ho (S1 ∪ S2)ᶜ (by
      intro i
      by_cases hi : i ∈ S1
      · simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
      · by_cases hi2 : i ∈ S2 <;>
          simp [C, hi, hi2, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact (g4D_compl ν hν x y hxy hxR _).1 hd this
  · right
    apply g4_expand ν hν hR z y (Ne.symm hyz) hzR hyR S2
    apply g4_key2 ν hν C z y ho S2
    intro i
    by_cases hi : i ∈ S1
    · simp [C, hi, hdis i hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
    · by_cases hi2 : i ∈ S2 <;>
        simp [C, hi, hi2, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]

theorem g4_singleton (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (hR : 3 ≤ (Set.range ν).ncard) : ∃ j : ι, g4Dec ν {j} := by
  have hne : (Set.range ν).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x, hxR⟩ := hne
  obtain ⟨y, hyR, hyx, -⟩ := g4_third ν hR x x
  have main : ∀ n, ∀ S : Finset ι, S.card = n → g4Dec ν S → ∃ j : ι, g4Dec ν {j} := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hcard hS
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · rw [Finset.card_eq_zero] at hcard
          subst hcard
          exact absurd (hS x hxR y hyR (Ne.symm hyx)) (g4D_empty ν hν x y (Ne.symm hyx) hxR hyR)
        · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hcard
          exact ⟨j, hS⟩
      · have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨j, hj⟩ := hSne
        have hsplit : S = {j} ∪ S.erase j := by
          rw [Finset.singleton_union, Finset.insert_erase hj]
        have hdisj : Disjoint ({j} : Finset ι) (S.erase j) := by simp
        rw [hsplit] at hS
        rcases g4_contract ν hν hR _ _ hdisj hS with h1 | h2
        · exact ⟨j, h1⟩
        · exact ih (S.erase j).card (by rw [Finset.card_erase_of_mem hj]; omega) _ rfl h2
  exact main _ Finset.univ rfl (fun u hu v hv huv => g4D_univ ν hν u v huv hu)

theorem theorem_1_core (ν : StrictVotingProcedure ι A)
    (hp : 3 ≤ (Set.range ν).ncard) :
    StrictStrategyProof ν ↔ StrictDictatorial ν := by
  constructor
  · intro hν
    obtain ⟨j, hj⟩ := g4_singleton ν hν hp
    refine ⟨j, fun C y hyR => ?_⟩
    by_cases hxy : ν C = y
    · rw [hxy]; exact ((C j).1.total y y).elim id id
    · by_contra hn
      classical
      let T : Finset ι := Finset.univ.filter (fun i => (C i).1.rel (ν C) y)
      have hT := g4_key2 ν hν C (ν C) y rfl T (fun i => by simp [T])
      have hjT : j ∉ T := by simp [T, hn]
      have hsub : T ⊆ ({j} : Finset ι)ᶜ := by
        intro i hi
        simp only [Finset.mem_compl, Finset.mem_singleton]
        rintro rfl; exact hjT hi
      have h1 := g4D_mono ν hν _ _ _ _ hsub hT
      have h2 := hj y hyR (ν C) ⟨C, rfl⟩ (Ne.symm hxy)
      exact (g4D_compl ν hν y (ν C) (Ne.symm hxy) hyR {j}).1 h2 h1
  · rintro ⟨j, hj⟩ C i c ⟨h1, h2⟩
    have a1 := hj C (ν (Function.update C i c)) ⟨_, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact h2 a1
    · have a2 := hj (Function.update C i c) (ν C) ⟨_, rfl⟩
      rw [Function.update_of_ne (Ne.symm hij)] at a2
      have heq := (C j).2 _ _ a2 (hj C _ ⟨_, rfl⟩)
      rw [heq] at h2
      exact h2 (((C i).1.total _ _).elim id id)

end

end GSCore

section Transfer
open StrategyProofArrow.Correspondence

/-- strict part of a strong order -/
def dtoS {A : Type*} (R : StrongOrder A) : A → A → Prop := fun x y => R.1.rel x y ∧ x ≠ y

theorem dtoS_sto {A : Type*} (R : StrongOrder A) : IsStrictTotalOrder A (dtoS R) := by
  apply dsto_mk
  · intro a b h1 h2
    by_contra hne
    rcases R.1.total a b with h | h
    · exact h1 ⟨h, hne⟩
    · exact h2 ⟨h, Ne.symm hne⟩
  · intro a h; exact h.2 rfl
  · intro a b c h1 h2
    refine ⟨R.1.trans _ _ _ h1.1 h2.1, ?_⟩
    rintro rfl
    exact h1.2 (R.2 _ _ h1.1 h2.1)

/-- strong order from a strict total order -/
def dofS {A : Type*} (r : A → A → Prop) (h : IsStrictTotalOrder A r) : StrongOrder A :=
  ⟨{ rel := fun x y => r x y ∨ x = y
     total := by
       intro x y
       rcases dsto_tri h x y with h1 | h1 | h1
       · exact Or.inl (Or.inl h1)
       · exact Or.inl (Or.inr h1)
       · exact Or.inr (Or.inl h1)
     trans := by
       rintro x y z (h1 | rfl) (h2 | rfl)
       · exact Or.inl (dsto_trans h h1 h2)
       · exact Or.inl h1
       · exact Or.inl h2
       · exact Or.inr rfl },
   by
     rintro x y (h1 | rfl) (h2 | h2)
     · exact (dsto_asymm h h1 h2).elim
     · exact h2.symm
     · rfl
     · rfl⟩

theorem dtoS_ofS {A : Type*} (r : A → A → Prop) (h : IsStrictTotalOrder A r) :
    dtoS (dofS r h) = r := by
  funext x y
  apply propext
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact h1
    · exact absurd h1 h2
  · intro h1
    refine ⟨Or.inl h1, ?_⟩
    rintro rfl; exact dsto_irr h _ h1

theorem dstrict_iff {A : Type*} (R : StrongOrder A) (x y : A) :
    R.1.strict x y ↔ dtoS R x y := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro rfl; exact h2 h1
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h3 => h2 (R.2 _ _ h1 h3)⟩

/-- the transferred strict voting procedure -/
def dnu {ι A : Type*} (f : (ι → A → A → Prop) → A) : StrongProfile ι A → A :=
  fun C => f (fun i => dtoS (C i))

theorem dnu_prof {ι A : Type*} (f : (ι → A → A → Prop) → A) (P : ι → A → A → Prop)
    (hP : IsPrefProfile P) : dnu f (fun i => dofS (P i) (hP i)) = f P := by
  simp only [dnu, dtoS_ofS]

theorem dnu_range {ι A : Type*} (f : (ι → A → A → Prop) → A) :
    Set.range (dnu f) = range f := by
  ext x
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨_, fun i => dtoS_sto (C i), rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨_, dnu_prof f P hP⟩

theorem dtoS_update {ι A : Type*} [DecidableEq ι] (C : StrongProfile ι A) (i : ι)
    (c : StrongOrder A) :
    (fun j => dtoS (Function.update C i c j)) = Function.update (fun j => dtoS (C j)) i (dtoS c) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem dofS_update {ι A : Type*} [DecidableEq ι] (f : (ι → A → A → Prop) → A) (P : ι → A → A → Prop)
    (hP : IsPrefProfile P) (i : ι) (r : A → A → Prop) (hr : IsStrictTotalOrder A r) :
    dnu f (Function.update (fun j => dofS (P j) (hP j)) i (dofS r hr)) =
      f (Function.update P i r) := by
  simp only [dnu]
  rw [dtoS_update]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp [dtoS_ofS]
  · simp [Function.update_of_ne h, dtoS_ofS]

theorem dsp_iff {ι A : Type*} [DecidableEq ι] (f : (ι → A → A → Prop) → A) :
    StrategyProofArrow.WeakGS.StrictStrategyProof (dnu f) ↔ IncentiveCompatible f := by
  constructor
  · intro H P hP i r' hr' hc
    apply H (fun j => dofS (P j) (hP j)) i (dofS r' hr')
    rw [dstrict_iff, dofS_update f P hP i r' hr', dnu_prof f P hP]
    show dtoS (dofS (P i) (hP i)) _ _
    rw [dtoS_ofS]; exact hc
  · intro H C i c hc
    rw [dstrict_iff] at hc
    apply H _ (fun j => dtoS_sto (C j)) i (dtoS c) (dtoS_sto c)
    have : dnu f (Function.update C i c) = f (Function.update (fun j => dtoS (C j)) i (dtoS c)) := by
      simp only [dnu]; rw [dtoS_update]
    rw [this] at hc
    exact hc

theorem ddict_iff {ι A : Type*} (f : (ι → A → A → Prop) → A) :
    StrategyProofArrow.WeakGS.StrictDictatorial (dnu f) ↔ Dictatorial f := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun P hP => ⟨dmem_range f hP, fun y hy hne => ?_⟩⟩
    have h := hi (fun j => dofS (P j) (hP j)) y (by rw [dnu_range]; exact hy)
    rw [dnu_prof f P hP] at h
    rcases h with h | h
    · exact h
    · exact absurd h.symm hne
  · rintro ⟨i, hi⟩
    refine ⟨i, fun C y hy => ?_⟩
    rw [dnu_range] at hy
    have hP : IsPrefProfile (fun j => dtoS (C j)) := fun j => dtoS_sto (C j)
    by_cases hne : y = dnu f C
    · rw [hne]; exact ((C i).1.total _ _).elim id id
    · exact ((hi _ hP).2 y hy hne).1

theorem theorem_1_main {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι)
    (f : (ι → A → A → Prop) → A) (hp : 3 ≤ (range f).ncard) :
    IncentiveCompatible f ↔ Dictatorial f := by
  rw [← dsp_iff, ← ddict_iff]
  apply StrategyProofArrow.Dictatorship.theorem_1_core
  rw [dnu_range]; exact hp

theorem lemma_5_main {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f := by
  haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  by_cases hr : range f = Set.univ
  · left
    refine ⟨hr, (theorem_1_main hn f ?_).1 hsp⟩
    rw [hr, Set.ncard_univ, Nat.card_eq_fintype_card]; exact hm
  · right
    refine ⟨?_, lemma_1_core f hsp⟩
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 hr
    exact ⟨x, fun P hP h => hx (h ▸ dmem_range f hP)⟩

theorem lemma_4_main {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : Fintype.card A = 3)
    (hind : ∀ g : (ι → A → A → Prop) → A, IncentiveCompatible g →
      FullyDictatorial g ∨ StrongAltExcluding g)
    (f : (Option ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f :=
  lemma_5_main (by rw [Fintype.card_option]; omega) (by omega) f hp hsp

end Transfer

end StrategyProofArrow.Dictatorship

open StrategyProofArrow.Dictatorship
open AGT

theorem solution {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι)
    (f : (ι → A → A → Prop) → A) (hp : 3 ≤ (range f).ncard) :
    IncentiveCompatible f ↔ Dictatorial f := by
  exact theorem_1_main hn f hp
