-- Prove2me | solution 2 for WeightedEdgeColor.lemma_large_edge_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T13:04:15.771811+00:00
-- url     : https://prove2.me/submissions/c46b6a19-b28f-49db-b34b-e12600c4697d

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Theorems.Thm_Nibble_local_almost_perfect_matching

set_option autoImplicit false

section SecInst

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Finset

namespace WeightedEdgeColor.LRN

variable {V E 𝒞 : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype 𝒞]
  [DecidableEq 𝒞] {Ks Dp : ℕ}

abbrev Op (E 𝒞 : Type) (Ks Dp : ℕ) := (E × 𝒞 × Fin Ks × Fin Ks) ⊕ (E × Fin Dp)
abbrev St (V E 𝒞 : Type) (Ks Dp : ℕ) := (V × 𝒞 × Fin Ks) ⊕ (E × Fin Dp)

def job : Op E 𝒞 Ks Dp → E
  | .inl p => p.1
  | .inr q => q.1

def sl (P : E → Prop) [DecidablePred P] (src tgt : E → V) : Op E 𝒞 Ks Dp → Finset (St V E 𝒞 Ks Dp)
  | .inl p => if P p.1 then {.inl (src p.1, p.2.1, p.2.2.1), .inl (tgt p.1, p.2.1, p.2.2.2)} else ∅
  | .inr q => {.inr q}

def dum (o : Op E 𝒞 Ks Dp) : Prop := o.isRight = true

instance : DecidablePred (dum (E := E) (𝒞 := 𝒞) (Ks := Ks) (Dp := Dp)) :=
  fun o => inferInstanceAs (Decidable (o.isRight = true))

/-- total large fraction of an edge -/
noncomputable def sE (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ) (e : E) : ℝ := ∑ c, ∑ i, ∑ j, XL e c i j

noncomputable def xx (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ) (Dp : ℕ) : Op E 𝒞 Ks Dp → ℝ
  | .inl p => XL p.1 p.2.1 p.2.2.1 p.2.2.2
  | .inr q => (1 - sE XL q.1) / Dp

variable (P : E → Prop) [DecidablePred P] (src tgt : E → V)

theorem sl_card (o : Op E 𝒞 Ks Dp) : (sl P src tgt o).card ≤ 2 := by
  cases o with
  | inl p =>
    simp only [sl]
    split_ifs
    · exact (card_insert_le _ _).trans (by simp)
    · simp
  | inr q => simp [sl]

theorem mem_sl_inl (p : E × 𝒞 × Fin Ks × Fin Ks) (s : St V E 𝒞 Ks Dp) :
    s ∈ sl P src tgt (.inl p) ↔ P p.1 ∧ (s = .inl (src p.1, p.2.1, p.2.2.1) ∨ s = .inl (tgt p.1, p.2.1, p.2.2.2)) := by
  simp only [sl]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem mem_sl_inr (q : E × Fin Dp) (s : St V E 𝒞 Ks Dp) :
    s ∈ sl (𝒞 := 𝒞) (Ks := Ks) P src tgt (.inr q) ↔ s = .inr q := by
  simp [sl]

theorem priv (o : Op E 𝒞 Ks Dp) (ho : dum o) (o' : Op E 𝒞 Ks Dp) (hne : o' ≠ o) :
    Disjoint (sl P src tgt o) (sl P src tgt o') := by
  cases o with
  | inl p => simp [dum] at ho
  | inr q =>
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [mem_sl_inr] at hs
    subst hs
    cases o' with
    | inl p' => rw [mem_sl_inl] at hs'; rcases hs'.2 with h | h <;> cases h
    | inr q' => rw [mem_sl_inr] at hs'; cases hs'; exact hne rfl

variable (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ)

theorem xx_nonneg (h0 : ∀ e c i j, 0 ≤ XL e c i j) (h1 : ∀ e, sE XL e ≤ 1) (o : Op E 𝒞 Ks Dp) :
    0 ≤ xx XL Dp o := by
  cases o with
  | inl p => exact h0 _ _ _ _
  | inr q => simp only [xx]; exact div_nonneg (by linarith [h1 q.1]) (Nat.cast_nonneg _)

theorem sum_inl (f : E × 𝒞 × Fin Ks × Fin Ks → ℝ) :
    ∑ p, f p = ∑ e, ∑ c, ∑ i, ∑ j, f (e, c, i, j) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Fintype.sum_prod_type]

theorem mass_eq (hDp : 0 < Dp) (e : E) :
    ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => job o = e), xx XL Dp o = 1 := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, sum_inl, Fintype.sum_prod_type]
  simp only [job, xx]
  rw [Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  rw [Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp only [if_true]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (Dp : ℝ) ≠ 0 := by exact_mod_cast hDp.ne'
  unfold sE
  field_simp
  ring


theorem ite_or_le (A B : Prop) [Decidable A] [Decidable B] (y : ℝ) (hy : 0 ≤ y) :
    (if A ∨ B then y else 0) ≤ (if A then y else 0) + (if B then y else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB, hy]

theorem load_le (h0 : ∀ e c i j, 0 ≤ XL e c i j) (v : V) (c : 𝒞) (i : Fin Ks) :
    ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => (Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl P src tgt o), xx XL Dp o ≤
      ∑ e ∈ univ.filter (fun e => src e = v), ∑ j, XL e c i j +
        ∑ e ∈ univ.filter (fun e => tgt e = v), ∑ j, XL e c j i := by
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  have hr : ∀ q : E × Fin Dp, ((Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl (𝒞 := 𝒞) (Ks := Ks) P src tgt (.inr q)) = False := by
    intro q; simp [mem_sl_inr]
  simp only [hr, if_false, Finset.sum_const_zero, add_zero]
  calc ∑ p : E × 𝒞 × Fin Ks × Fin Ks, (if (Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl P src tgt (.inl p) then xx XL Dp (.inl p) else 0)
      ≤ ∑ p : E × 𝒞 × Fin Ks × Fin Ks, ((if src p.1 = v ∧ p.2.1 = c ∧ p.2.2.1 = i then XL p.1 p.2.1 p.2.2.1 p.2.2.2 else 0) +
          (if tgt p.1 = v ∧ p.2.1 = c ∧ p.2.2.2 = i then XL p.1 p.2.1 p.2.2.1 p.2.2.2 else 0)) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        refine le_trans ?_ (ite_or_le _ _ _ (h0 _ _ _ _))
        by_cases hm : (Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl P src tgt (.inl p)
        · rw [if_pos hm]
          rw [mem_sl_inl] at hm
          rw [if_pos]
          · rfl
          rcases hm.2 with h | h
          · simp only [Sum.inl.injEq, Prod.mk.injEq] at h
            exact Or.inl ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
          · simp only [Sum.inl.injEq, Prod.mk.injEq] at h
            exact Or.inr ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
        · rw [if_neg hm]; split_ifs <;> first | exact le_rfl | exact h0 _ _ _ _
    _ = _ := by
        rw [Finset.sum_add_distrib, sum_inl, sum_inl, Finset.sum_filter, Finset.sum_filter]
        congr 1
        · refine Finset.sum_congr rfl (fun e _ => ?_)
          by_cases he : src e = v
          · simp only [he, true_and, if_true]
            rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
            rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
            simp
          · simp [he]
        · refine Finset.sum_congr rfl (fun e _ => ?_)
          by_cases he : tgt e = v
          · simp only [he, true_and, if_true]
            rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
            simp
          · simp [he]

theorem load_inr_le (h0 : ∀ e c i j, 0 ≤ XL e c i j) (q : E × Fin Dp) :
    ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => (Sum.inr q : St V E 𝒞 Ks Dp) ∈ sl P src tgt o), xx XL Dp o ≤
      1 / Dp := by
  have hs : univ.filter (fun o : Op E 𝒞 Ks Dp => (Sum.inr q : St V E 𝒞 Ks Dp) ∈ sl P src tgt o) = {.inr q} := by
    ext o
    cases o with
    | inl p => simp [mem_sl_inl]
    | inr q' => simp [mem_sl_inr, eq_comm]
  rw [hs, Finset.sum_singleton]
  simp only [xx]
  have : 0 ≤ sE XL q.1 := Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => h0 _ _ _ _)))
  apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

theorem yw_le (h0 : ∀ e c i j, 0 ≤ XL e c i j) (h1 : ∀ e, sE XL e ≤ 1) (κ : ℝ) (hc : ∀ e c, ∑ i, ∑ j, XL e c i j ≤ κ)
    (hD : 1 / (Dp : ℝ) ≤ κ) (e : E) (t : St V E 𝒞 Ks Dp) :
    ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => job o = e ∧ t ∈ sl P src tgt o), xx XL Dp o ≤ κ := by
  cases t with
  | inr q =>
    calc _ ≤ ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => (Sum.inr q : St V E 𝒞 Ks Dp) ∈ sl P src tgt o), xx XL Dp o := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro o; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.2
          · intro o _ _; exact xx_nonneg XL h0 h1 o
      _ ≤ 1 / Dp := load_inr_le P src tgt XL h0 q
      _ ≤ κ := hD
  | inl a =>
    obtain ⟨v, c, i⟩ := a
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    have hr : ∀ q : E × Fin Dp, (job (𝒞 := 𝒞) (Ks := Ks) (.inr q) = e ∧ (Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl (𝒞 := 𝒞) (Ks := Ks) P src tgt (.inr q)) = False := by
      intro q; simp [mem_sl_inr]
    simp only [hr, if_false, Finset.sum_const_zero, add_zero]
    calc ∑ p : E × 𝒞 × Fin Ks × Fin Ks, (if job (Dp := Dp) (.inl p) = e ∧ (Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl P src tgt (.inl p) then xx XL Dp (.inl p) else 0)
        ≤ ∑ p : E × 𝒞 × Fin Ks × Fin Ks, (if p.1 = e ∧ p.2.1 = c then XL p.1 p.2.1 p.2.2.1 p.2.2.2 else 0) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          by_cases hm : job (Dp := Dp) (.inl p) = e ∧ (Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl P src tgt (.inl p)
          · rw [if_pos hm, if_pos]
            · rfl
            refine ⟨hm.1, ?_⟩
            have := hm.2
            rw [mem_sl_inl] at this
            rcases this.2 with h | h
            · simp only [Sum.inl.injEq, Prod.mk.injEq] at h; exact h.2.1.symm
            · simp only [Sum.inl.injEq, Prod.mk.injEq] at h; exact h.2.1.symm
          · rw [if_neg hm]; split_ifs <;> first | exact le_rfl | exact h0 _ _ _ _
      _ = ∑ i, ∑ j, XL e c i j := by
          rw [sum_inl]
          rw [Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
          rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
          simp
      _ ≤ κ := hc e c


theorem two_slots (s t : St V E 𝒞 Ks Dp) (hst : s ≠ t) (o : Op E 𝒞 Ks Dp) (hs : s ∈ sl P src tgt o)
    (ht : t ∈ sl P src tgt o) :
    ∃ p, o = .inl p ∧ ((s = .inl (src p.1, p.2.1, p.2.2.1) ∧ t = .inl (tgt p.1, p.2.1, p.2.2.2)) ∨
      (s = .inl (tgt p.1, p.2.1, p.2.2.2) ∧ t = .inl (src p.1, p.2.1, p.2.2.1))) := by
  cases o with
  | inr q => rw [mem_sl_inr] at hs ht; exact absurd (hs.trans ht.symm) hst
  | inl p =>
    refine ⟨p, rfl, ?_⟩
    rw [mem_sl_inl] at hs ht
    rcases hs.2 with h1 | h1 <;> rcases ht.2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hst
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hst

theorem same_job (ends : E → Sym2 V) (hinj : Function.Injective ends)
    (hends : ∀ e, ends e = s(src e, tgt e)) (s t : St V E 𝒞 Ks Dp) (hst : s ≠ t) (o o' : Op E 𝒞 Ks Dp)
    (hs : s ∈ sl P src tgt o) (ht : t ∈ sl P src tgt o) (hs' : s ∈ sl P src tgt o')
    (ht' : t ∈ sl P src tgt o') : job o = job o' := by
  obtain ⟨p, rfl, hp⟩ := two_slots P src tgt s t hst o hs ht
  obtain ⟨p', rfl, hp'⟩ := two_slots P src tgt s t hst o' hs' ht'
  simp only [job]
  apply hinj
  rw [hends, hends]
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hp' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
    rw [h1] at h1' <;> rw [h2] at h2' <;> simp only [Sum.inl.injEq, Prod.mk.injEq] at h1' h2'
  · rw [h1'.1, h2'.1]
  · rw [h1'.1, h2'.1, Sym2.eq_swap]
  · rw [h1'.1, h2'.1, Sym2.eq_swap]
  · rw [h1'.1, h2'.1]

theorem kw_le (ends : E → Sym2 V) (hinj : Function.Injective ends)
    (hends : ∀ e, ends e = s(src e, tgt e)) (h0 : ∀ e c i j, 0 ≤ XL e c i j) (h1 : ∀ e, sE XL e ≤ 1)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hyw : ∀ e t, ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => job o = e ∧ t ∈ sl P src tgt o), xx XL Dp o ≤ κ)
    (s t : St V E 𝒞 Ks Dp) (hst : s ≠ t) :
    ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => s ∈ sl P src tgt o ∧ t ∈ sl P src tgt o), xx XL Dp o ≤ κ := by
  by_cases hex : ∃ o : Op E 𝒞 Ks Dp, s ∈ sl P src tgt o ∧ t ∈ sl P src tgt o
  · obtain ⟨o₀, hs₀, ht₀⟩ := hex
    refine le_trans ?_ (hyw (job o₀) s)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro o
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      exact ⟨same_job P src tgt ends hinj hends s t hst o o₀ h.1 h.2 hs₀ ht₀, h.1⟩
    · intro o _ _; exact xx_nonneg XL h0 h1 o
  · push_neg at hex
    rw [Finset.sum_eq_zero]
    · exact hκ
    · intro o ho
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
      exact absurd ho.2 (hex o ho.1)

/-- the large edges at `v` -/
def LEs (ends : E → Sym2 V) (v : V) : Finset E := univ.filter (fun f => P f ∧ v ∈ ends f)

theorem Nb_sub (ends : E → Sym2 V) (hends : ∀ e, ends e = s(src e, tgt e)) (e : E)
    {_inst : DecidablePred (fun f => ∃ o o' : Op E 𝒞 Ks Dp, job o = e ∧ job o' = f ∧
      ¬ Disjoint (sl P src tgt o) (sl P src tgt o'))} :
    insert e (univ.filter (fun f => ∃ o o' : Op E 𝒞 Ks Dp, job o = e ∧ job o' = f ∧
      ¬ Disjoint (sl P src tgt o) (sl P src tgt o'))) ⊆
      insert e (LEs P ends (src e) ∪ LEs P ends (tgt e)) := by
  intro f hf
  rw [Finset.mem_insert] at hf ⊢
  rcases hf with hf | hf
  · exact Or.inl hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  obtain ⟨o, o', hoe, hof, hnd⟩ := hf
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨s, hs, hs'⟩ := hnd
  cases o with
  | inr q =>
    rw [mem_sl_inr] at hs
    subst hs
    cases o' with
    | inl p' => rw [mem_sl_inl] at hs'; rcases hs'.2 with h | h <;> cases h
    | inr q' =>
      rw [mem_sl_inr] at hs'
      cases hs'
      left; simp only [job] at hoe hof; rw [← hof, hoe]
  | inl p =>
    rw [mem_sl_inl] at hs
    simp only [job] at hoe
    subst hoe
    cases o' with
    | inr q' => rw [mem_sl_inr] at hs'; rcases hs.2 with h | h <;> (rw [h] at hs'; cases hs')
    | inl p' =>
      rw [mem_sl_inl] at hs'
      simp only [job] at hof
      subst hof
      right
      rw [Finset.mem_union]
      simp only [LEs, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hs.2 with h | h <;> rcases hs'.2 with h' | h' <;> rw [h] at h' <;>
        simp only [Sum.inl.injEq, Prod.mk.injEq] at h'
      · left; exact ⟨hs'.1, by rw [hends, h'.1]; exact Sym2.mem_mk_left _ _⟩
      · left; exact ⟨hs'.1, by rw [hends, h'.1]; exact Sym2.mem_mk_right _ _⟩
      · right; exact ⟨hs'.1, by rw [hends, h'.1]; exact Sym2.mem_mk_left _ _⟩
      · right; exact ⟨hs'.1, by rw [hends, h'.1]; exact Sym2.mem_mk_right _ _⟩

theorem As_card (ends : E → Sym2 V) (hends : ∀ e, ends e = s(src e, tgt e)) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ v, (LEs P ends v).card ≤ B) (s : St V E 𝒞 Ks Dp)
    {_inst : DecidablePred (fun e => ∃ o : Op E 𝒞 Ks Dp, job o = e ∧ s ∈ sl P src tgt o)} :
    (univ.filter (fun e => ∃ o : Op E 𝒞 Ks Dp, job o = e ∧ s ∈ sl P src tgt o)).card ≤ B := by
  cases s with
  | inl a =>
    obtain ⟨v, c, i⟩ := a
    refine le_trans (Finset.card_le_card ?_) (hB v)
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨o, hoe, hs⟩ := he
    cases o with
    | inr q => rw [mem_sl_inr] at hs; cases hs
    | inl p =>
      rw [mem_sl_inl] at hs
      simp only [job] at hoe
      subst hoe
      simp only [LEs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hs.1, ?_⟩
      rw [hends]
      rcases hs.2 with h | h <;> simp only [Sum.inl.injEq, Prod.mk.injEq] at h <;> rw [h.1]
      · exact Sym2.mem_mk_left _ _
      · exact Sym2.mem_mk_right _ _
  | inr q =>
    refine le_trans (Finset.card_le_card (t := {q.1}) ?_) (by simpa using hB1)
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨o, hoe, hs⟩ := he
    cases o with
    | inl p => rw [mem_sl_inl] at hs; rcases hs.2 with h | h <;> cases h
    | inr q' =>
      rw [mem_sl_inr] at hs
      cases hs
      simp only [job] at hoe
      simp [hoe]

theorem slots_card (e : E) {_inst : DecidablePred (fun s : St V E 𝒞 Ks Dp => ∃ o : Op E 𝒞 Ks Dp, job o = e ∧ s ∈ sl P src tgt o)} :
    (univ.filter (fun s : St V E 𝒞 Ks Dp => ∃ o : Op E 𝒞 Ks Dp, job o = e ∧ s ∈ sl P src tgt o)).card ≤
      2 * (Fintype.card 𝒞 * Ks) + Dp := by
  have hsub : univ.filter (fun s : St V E 𝒞 Ks Dp => ∃ o : Op E 𝒞 Ks Dp, job o = e ∧ s ∈ sl P src tgt o) ⊆
      (univ.image (fun a : 𝒞 × Fin Ks => (Sum.inl (src e, a.1, a.2) : St V E 𝒞 Ks Dp)) ∪
        univ.image (fun a : 𝒞 × Fin Ks => (Sum.inl (tgt e, a.1, a.2) : St V E 𝒞 Ks Dp))) ∪
        univ.image (fun k : Fin Dp => (Sum.inr (e, k) : St V E 𝒞 Ks Dp)) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨o, hoe, hs⟩ := hs
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    cases o with
    | inl p =>
      rw [mem_sl_inl] at hs
      simp only [job] at hoe
      subst hoe
      rcases hs.2 with h | h
      · exact Or.inl (Or.inl ⟨(p.2.1, p.2.2.1), h.symm⟩)
      · exact Or.inl (Or.inr ⟨(p.2.1, p.2.2.2), h.symm⟩)
    | inr q =>
      rw [mem_sl_inr] at hs
      simp only [job] at hoe
      subst hs hoe
      exact Or.inr ⟨q.2, rfl⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := Finset.card_image_le (s := (univ : Finset (𝒞 × Fin Ks)))
      (f := fun a : 𝒞 × Fin Ks => (Sum.inl (src e, a.1, a.2) : St V E 𝒞 Ks Dp))
    have h2 := Finset.card_image_le (s := (univ : Finset (𝒞 × Fin Ks)))
      (f := fun a : 𝒞 × Fin Ks => (Sum.inl (tgt e, a.1, a.2) : St V E 𝒞 Ks Dp))
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1 h2
    omega
  · refine le_trans Finset.card_image_le ?_
    simp

theorem groups_card (ends : E → Sym2 V) (hends : ∀ e, ends e = s(src e, tgt e)) (e : E)
    {_inst : DecidablePred (fun v => e ∈ LEs P ends v)} :
    (univ.filter (fun v => e ∈ LEs P ends v)).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := {src e, tgt e}) ?_) (Finset.card_insert_le _ _ |>.trans (by simp))
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, LEs] at hv
  have := hv.2
  rw [hends, Sym2.mem_iff] at this
  rcases this with h | h <;> simp [h]

theorem LEs_card (ends : E → Sym2 V) (w : E → ℝ) (β : ℝ) (hw : ∀ e, 0 ≤ w e) (hP : ∀ e, P e → β ≤ w e) (v : V) :
    ((LEs P ends v).card : ℝ) * β ≤ ∑ f ∈ univ.filter (fun f => v ∈ ends f), w f := by
  calc ((LEs P ends v).card : ℝ) * β = ∑ f ∈ LEs P ends v, β := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ f ∈ LEs P ends v, w f := Finset.sum_le_sum (fun f hf => hP f (by
        simp only [LEs, Finset.mem_filter] at hf; exact hf.2.1))
    _ ≤ ∑ f ∈ univ.filter (fun f => v ∈ ends f), w f := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro f hf; simp only [LEs, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢; exact hf.2
        · intro f _ _; exact hw f

theorem rmass_eq (e : E) :
    ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => job o = e ∧ ¬ dum o), xx XL Dp o = sE XL e := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, sum_inl]
  have hr : ∀ q : E × Fin Dp, ¬ (job (𝒞 := 𝒞) (Ks := Ks) (.inr q) = e ∧ ¬ dum (𝒞 := 𝒞) (Ks := Ks) (.inr q)) := by
    intro q h; exact h.2 (by simp [dum])
  simp only [hr, if_false, Finset.sum_const_zero, add_zero]
  have hl : ∀ p : E × 𝒞 × Fin Ks × Fin Ks, (job (Dp := Dp) (.inl p) = e ∧ ¬ dum (Dp := Dp) (.inl p)) ↔ p.1 = e := by
    intro p; simp [job, dum]
  simp only [hl]
  rw [Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp [xx, sE]

end WeightedEdgeColor.LRN

end SecInst

section SecArith

set_option autoImplicit false

namespace WeightedEdgeColor.LRN

theorem log_le_two_sqrt (y : ℝ) (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [← Real.log_rpow hs]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hy.le]
  linarith

/-- the logarithmic factor is at most `B √n` -/
theorem logD_le (A T : ℝ) (D : ℕ) (hA : 0 ≤ A) (hT : 1 ≤ T) (hD1 : 1 ≤ D) (hD : (D : ℝ) ≤ (A + 1) * T ^ 2) :
    Real.log D + 1 ≤ (1 + 2 * Real.sqrt (A + 1)) * T := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  have h1 := log_le_two_sqrt D hDpos
  have h2 : Real.sqrt D ≤ Real.sqrt (A + 1) * T := by
    calc Real.sqrt D ≤ Real.sqrt ((A + 1) * T ^ 2) := Real.sqrt_le_sqrt hD
      _ = Real.sqrt (A + 1) * T := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by linarith)]
  have h3 : 0 ≤ Real.sqrt (A + 1) := Real.sqrt_nonneg _
  nlinarith

theorem kappa_conds (Cp c₁ A B T L : ℝ) (D : ℕ) (hCp : 0 < Cp) (hc₁ : 0 < c₁) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : 1 ≤ T) (hL0 : 0 ≤ L) (hL : L ≤ B * T) (hD : (D : ℝ) ≤ (A + 1) * T ^ 2)
    (hT1 : Cp * B / c₁ ≤ T) (hT2 : Cp ^ 2 * (A + 1) * B / c₁ ≤ T) :
    Cp / T ^ 2 * L ≤ c₁ ∧ (Cp / T ^ 2) ^ 2 * D * L ≤ c₁ := by
  have hT0 : 0 < T := by linarith
  have hT2' : 0 < T ^ 2 := by positivity
  constructor
  · calc Cp / T ^ 2 * L ≤ Cp / T ^ 2 * (B * T) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = Cp * B / T := by field_simp
      _ ≤ c₁ := by rw [div_le_iff₀ hT0]; rw [div_le_iff₀ hc₁] at hT1; linarith
  · calc (Cp / T ^ 2) ^ 2 * D * L ≤ (Cp / T ^ 2) ^ 2 * ((A + 1) * T ^ 2) * (B * T) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hD (by positivity)) hL hL0 (by positivity)
      _ = Cp ^ 2 * (A + 1) * B / T := by field_simp
      _ ≤ c₁ := by rw [div_le_iff₀ hT0]; rw [div_le_iff₀ hc₁] at hT2; linarith

theorem err_arith (c β ε T L m : ℝ) (hc : 0 ≤ c) (hβ : 0 < β) (hε : 0 < ε) (hT : 1 ≤ T) (hL0 : 0 ≤ L)
    (B : ℝ) (hB : 0 ≤ B) (hL : L ≤ B * T) (hm0 : 0 ≤ m) (hm : m ≤ T ^ 2 / β)
    (hT1 : 4 * c * B / ε ≤ T) (hT2 : 16 * c ^ 2 * B / (β * ε ^ 2) ≤ T) :
    c * (Real.sqrt (m * L) + L) ≤ ε / 2 * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have h1 : c * L ≤ ε / 4 * T ^ 2 := by
    rw [div_le_iff₀ hε] at hT1
    calc c * L ≤ c * (B * T) := mul_le_mul_of_nonneg_left hL hc
      _ = (c * B) * T := by ring
      _ ≤ (ε * T / 4) * T := by apply mul_le_mul_of_nonneg_right _ hT0.le; linarith
      _ = ε / 4 * T ^ 2 := by ring
  have h2 : c * Real.sqrt (m * L) ≤ ε / 4 * T ^ 2 := by
    have hsq : c * Real.sqrt (m * L) = Real.sqrt (c ^ 2 * (m * L)) := by
      rw [Real.sqrt_mul (sq_nonneg c) (m * L), Real.sqrt_sq hc]
    rw [hsq]
    have hbound : c ^ 2 * (m * L) ≤ (ε / 4 * T ^ 2) ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hT2
      calc c ^ 2 * (m * L) ≤ c ^ 2 * (T ^ 2 / β * (B * T)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hm hL hL0 (by positivity)
        _ = (16 * c ^ 2 * B / (β * ε ^ 2)) * T ^ 3 * (ε ^ 2 / 16) := by field_simp
        _ ≤ T * T ^ 3 * (ε ^ 2 / 16) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
        _ = (ε / 4 * T ^ 2) ^ 2 := by ring
    calc Real.sqrt (c ^ 2 * (m * L)) ≤ Real.sqrt ((ε / 4 * T ^ 2) ^ 2) := Real.sqrt_le_sqrt hbound
      _ = ε / 4 * T ^ 2 := Real.sqrt_sq (by positivity)
  nlinarith

end WeightedEdgeColor.LRN

end SecArith

section SecMain

set_option autoImplicit false

set_option maxHeartbeats 2000000 in
open WeightedEdgeColor WeightedEdgeColor.LRN Finset in
theorem solution (C₁ σ β Cm ε : ℝ) (Ks : ℕ)
    (hC₁ : 0 < C₁) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hCm : 0 < Cm) (hε : 0 < ε) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (b : V → 𝒞 → Fin Ks → ℝ) (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ),
      (∀ e c i j, 0 ≤ XL e c i j) →
      (∀ e c i j, XL e c i j ≠ 0 → β ≤ G.w e ∧ G.w e ≤ b (src e) c i ∧ G.w e ≤ b (tgt e) c j) →
      (∀ e, ∑ c, ∑ i, ∑ j, XL e c i j ≤ 1) →
      (∀ e c, ∑ i, ∑ j, XL e c i j ≤ Cm / n) →
      (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
         + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ) →
      ∃ ψ : E → Option (𝒞 × Fin Ks × Fin Ks),
        -- only options of positive fraction are chosen
        (∀ e c i j, ψ e = some (c, i, j) → 0 < XL e c i j) ∧
        -- no slot is used twice
        (∀ (e e' : E) (v : V) (c : 𝒞) (i : Fin Ks),
          (∃ j, (src e = v ∧ ψ e = some (c, i, j)) ∨ (tgt e = v ∧ ψ e = some (c, j, i))) →
          (∃ j, (src e' = v ∧ ψ e' = some (c, i, j)) ∨ (tgt e' = v ∧ ψ e' = some (c, j, i))) →
          e = e') ∧
        -- the large edges left unchosen carry little more weight than their unassigned fractions
        ∀ v, ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e ∧ ψ e = none), G.w e ≤
          ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e),
            G.w e * (1 - ∑ c, ∑ i, ∑ j, XL e c i j) + ε * n + K * n ^ (2 / 3 : ℝ) := by
  obtain ⟨c₁, c₂, hc₁, hLAPM⟩ := Nibble.local_almost_perfect_matching σ (min (ε / 2) 1) hσ0 hσ1.le
    (lt_min (by linarith) one_pos) (min_le_right _ _)
  set ε' := min (ε / 2) 1 with hε'
  have hε'2 : ε' ≤ ε / 2 := min_le_left _ _
  have hε'0 : 0 < ε' := lt_min (by linarith) one_pos
  set Cp := max Cm 1 with hCp
  have hCp1 : 1 ≤ Cp := le_max_right _ _
  have hCmCp : Cm ≤ Cp := le_max_left _ _
  set cp := max c₂ 0 with hcp
  have hcp0 : 0 ≤ cp := le_max_right _ _
  set A : ℝ := 2 * C₁ * Ks + 2 / β + 4 with hA
  have hA0 : 0 ≤ A := by positivity
  set B : ℝ := 1 + 2 * Real.sqrt (A + 1) with hB
  have hB0 : 0 ≤ B := by positivity
  set X : ℝ := Cp * B / c₁ + Cp ^ 2 * (A + 1) * B / c₁ + 4 * cp * B / ε +
    16 * cp ^ 2 * B / (β * ε ^ 2) + 1 with hX
  have hXa : 0 ≤ Cp * B / c₁ := by positivity
  have hXb : 0 ≤ Cp ^ 2 * (A + 1) * B / c₁ := by positivity
  have hXc : 0 ≤ 4 * cp * B / ε := by positivity
  have hXd : 0 ≤ 16 * cp ^ 2 * B / (β * ε ^ 2) := by positivity
  have hX1 : 1 ≤ X := by linarith
  refine ⟨max (1 / (1 - σ)) (X ^ 2), 0, ?_⟩
  intro V E _ _ _ _ G hG src tgt hends n hn hW 𝒞 _ _ hC b XL hXL0 hXLs hXL1 hXLc hload
  have hnX : X ^ 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnσ : 1 / (1 - σ) ≤ n := le_trans (le_max_left _ _) hn
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
  have hn1 : 1 ≤ n := by linarith
  have hn0 : 0 < n := by linarith
  set T := Real.sqrt n with hT
  have hTX : X ≤ T := Real.le_sqrt_of_sq_le hnX
  have hTsq : T ^ 2 = n := Real.sq_sqrt hn0.le
  have hT1 : 1 ≤ T := le_trans hX1 hTX
  set Dp : ℕ := ⌈n⌉₊ with hDp
  have hDpn : n ≤ Dp := Nat.le_ceil n
  have hDpn' : (Dp : ℝ) < n + 1 := Nat.ceil_lt_add_one hn0.le
  have hDp0 : 0 < Dp := by
    have : (0 : ℝ) < Dp := by linarith
    exact_mod_cast this
  set D : ℕ := ⌈A * n⌉₊ with hD
  have hDA : A * n ≤ D := Nat.le_ceil _
  have hDA' : (D : ℝ) < A * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hAn : A * n = 2 * C₁ * Ks * n + 2 / β * n + 4 * n := by rw [hA]; ring
  have hAn1 : 0 ≤ 2 * C₁ * Ks * n := by positivity
  have hAn2 : 0 ≤ 2 / β * n := by positivity
  have hAn4 : 4 * n ≤ A * n := by linarith
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hDle : (D : ℝ) ≤ (A + 1) * T ^ 2 := by
    rw [hTsq]
    have : (A + 1) * n = A * n + n := by ring
    linarith
  set κ := Cp / n with hκ
  have hκ0 : 0 < κ := by positivity
  set P : E → Prop := fun e => β ≤ G.w e with hP
  have hLEs : ∀ v, ((LEs P G.ends v).card : ℝ) ≤ n / β := by
    intro v
    have h := LEs_card P G.ends G.w β (fun e => (G.w_pos e).le) (fun e he => he) v
    rw [le_div_iff₀ hβ0]
    exact le_trans h (hW v)
  have hnβ' : n / β ≤ 2 / β * n := by
    have : n / β = 1 / β * n := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hn0.le
    exact div_le_div_of_nonneg_right (by norm_num) hβ0.le
  have hnβ : n / β ≤ A * n := by linarith
  have hLEsD : ∀ v, (LEs P G.ends v).card ≤ D := by
    intro v
    have : ((LEs P G.ends v).card : ℝ) ≤ D := le_trans (hLEs v) (le_trans hnβ hDA)
    exact_mod_cast this
  set L := Real.log D + 1 with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD1)
    linarith
  have hLB : L ≤ B * T := logD_le A T D hA0 hT1 hD1 hDle
  have hκT : κ = Cp / T ^ 2 := by rw [hTsq]
  obtain ⟨hk1, hk2⟩ := kappa_conds Cp c₁ A B T L D (by linarith) hc₁ hA0 hB0 hT1 hL0 hLB hDle
    (by linarith) (by linarith)
  rw [← hκT] at hk1 hk2
  -- the hypotheses of the nibble lemma
  have hXL1' : ∀ e, sE XL e ≤ 1 := hXL1
  have hκDp : 1 / (Dp : ℝ) ≤ κ := by
    rw [hκ, div_le_div_iff₀ (by exact_mod_cast hDp0) hn0]
    have : (Dp : ℝ) ≤ Cp * Dp := le_mul_of_one_le_left (by positivity) hCp1
    linarith
  have hcκ : ∀ e c, ∑ i, ∑ j, XL e c i j ≤ κ := by
    intro e c
    exact le_trans (hXLc e c) (div_le_div_of_nonneg_right hCmCp hn0.le)
  have hyw := yw_le (Dp := Dp) P src tgt XL hXL0 hXL1' κ hcκ hκDp
  have hloadO : ∀ s : St V E 𝒞 Ks Dp,
      ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => s ∈ sl P src tgt o), xx XL Dp o ≤ 1 - σ := by
    intro s
    cases s with
    | inl a =>
      obtain ⟨v, c, i⟩ := a
      exact le_trans (load_le P src tgt XL hXL0 v c i) (hload v c i)
    | inr q =>
      refine le_trans (load_inr_le P src tgt XL hXL0 q) ?_
      have h1σ : 0 < 1 - σ := by linarith
      rw [div_le_iff₀ (by exact_mod_cast hDp0)]
      rw [div_le_iff₀ h1σ] at hnσ
      have : n * (1 - σ) ≤ Dp * (1 - σ) := mul_le_mul_of_nonneg_right hDpn h1σ.le
      linarith
  have hC' : (Fintype.card 𝒞 : ℝ) * Ks ≤ C₁ * n * Ks :=
    mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)
  obtain ⟨M, hM1, hM2, hM3⟩ := hLAPM E (St V E 𝒞 Ks Dp) (Op E 𝒞 Ks Dp) V job (sl P src tgt) dum
    (LEs P G.ends) G.w (xx XL Dp) κ D
    (sl_card P src tgt) (fun o ho o' hne => priv P src tgt o ho o' hne)
    (fun e => ⟨(G.w_pos e).le, G.w_le_one e⟩) (xx_nonneg XL hXL0 hXL1') (mass_eq XL hDp0) hloadO hyw
    (kw_le P src tgt XL G.ends hG hends hXL0 hXL1' κ hκ0.le hyw)
    hκ0 hD1
    (fun e => by
      refine le_trans (Finset.card_le_card (Nb_sub P src tgt G.ends hends e)) ?_
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h1 := Finset.card_union_le (LEs P G.ends (src e)) (LEs P G.ends (tgt e))
      have : ((LEs P G.ends (src e) ∪ LEs P G.ends (tgt e)).card + 1 : ℝ) ≤ D := by
        have h2 : ((LEs P G.ends (src e) ∪ LEs P G.ends (tgt e)).card : ℝ) ≤
            (LEs P G.ends (src e)).card + (LEs P G.ends (tgt e)).card := by exact_mod_cast h1
        have h3 := hLEs (src e)
        have h4 := hLEs (tgt e)
        have h6 : 2 * (n / β) + 1 ≤ A * n := by
          have : 2 * (n / β) = 2 / β * n := by ring
          linarith
        linarith
      exact_mod_cast this)
    (fun s => As_card P src tgt G.ends hends D hD1 hLEsD s)
    (fun e => by
      refine le_trans (slots_card P src tgt e) ?_
      have : (2 * (Fintype.card 𝒞 * Ks) + Dp : ℝ) ≤ D := by
        have : 2 * C₁ * Ks * n + n + 1 ≤ A * n := by linarith
        have h7 : C₁ * n * Ks = C₁ * Ks * n := by ring
        linarith
      exact_mod_cast this)
    hLEsD
    (fun e => le_trans (groups_card P src tgt G.ends hends e) (by
      have : (2 : ℝ) ≤ D := by linarith
      exact_mod_cast this))
    hk1 hk2
  -- the choice function
  set ψ : E → Option (𝒞 × Fin Ks × Fin Ks) := fun e =>
    if h : ∃ a : 𝒞 × Fin Ks × Fin Ks, (Sum.inl (e, a) : Op E 𝒞 Ks Dp) ∈ M then some (Classical.choose h)
    else none with hψ
  have hψmem : ∀ e a, ψ e = some a → (Sum.inl (e, a) : Op E 𝒞 Ks Dp) ∈ M := by
    intro e a h
    simp only [hψ] at h
    split_ifs at h with h'
    · rw [← Option.some_inj.mp h]; exact Classical.choose_spec h'
  have hψnone : ∀ e, ψ e = none ↔ ¬ ∃ a : 𝒞 × Fin Ks × Fin Ks, (Sum.inl (e, a) : Op E 𝒞 Ks Dp) ∈ M := by
    intro e
    simp only [hψ]
    split_ifs with h
    · simp [h]
    · simp [h]
  have hpos : ∀ e c i j, ψ e = some (c, i, j) → 0 < XL e c i j := by
    intro e c i j h
    have := hM1 _ (hψmem e _ h)
    simpa [xx] using this
  refine ⟨ψ, hpos, ?_, ?_⟩
  · intro e e' v c i h h'
    have key : ∀ f : E, (∃ j, (src f = v ∧ ψ f = some (c, i, j)) ∨ (tgt f = v ∧ ψ f = some (c, j, i))) →
        ∃ a, (Sum.inl (f, a) : Op E 𝒞 Ks Dp) ∈ M ∧
          (Sum.inl (v, c, i) : St V E 𝒞 Ks Dp) ∈ sl P src tgt (Sum.inl (f, a)) := by
      rintro f ⟨j, ⟨hv, hf⟩ | ⟨hv, hf⟩⟩
      · refine ⟨(c, i, j), hψmem f _ hf, ?_⟩
        rw [mem_sl_inl]
        exact ⟨(hXLs f c i j (hpos f c i j hf).ne').1, Or.inl (by simp [hv])⟩
      · refine ⟨(c, j, i), hψmem f _ hf, ?_⟩
        rw [mem_sl_inl]
        exact ⟨(hXLs f c j i (hpos f c j i hf).ne').1, Or.inr (by simp [hv])⟩
    obtain ⟨a, haM, has⟩ := key e h
    obtain ⟨a', ha'M, ha's⟩ := key e' h'
    by_contra hne
    have hneo : (Sum.inl (e, a) : Op E 𝒞 Ks Dp) ≠ Sum.inl (e', a') := by
      intro heq
      simp only [Sum.inl.injEq, Prod.mk.injEq] at heq
      exact hne heq.1
    exact Finset.disjoint_left.mp (hM2 _ haM _ ha'M hneo).2 has ha's
  · intro v
    have h3 := hM3 v
    have hLEv : (G.inc v).filter (fun e => β ≤ G.w e) = LEs P G.ends v := by
      ext e; simp [WGraph.inc, LEs, hP, and_comm]
    have hcov : ∀ e, (∃ m ∈ M, job m = e ∧ ¬ dum m) ↔ ¬ ψ e = none := by
      intro e
      rw [hψnone, not_not]
      constructor
      · rintro ⟨m, hm, hje, hd⟩
        cases m with
        | inl p =>
          simp only [job] at hje
          subst hje
          exact ⟨p.2, hm⟩
        | inr q => exact absurd (by simp [dum]) hd
      · rintro ⟨a, ha⟩
        exact ⟨_, ha, rfl, by simp [dum]⟩
    have hlhs : ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e ∧ ψ e = none), G.w e =
        ∑ e ∈ LEs P G.ends v, G.w e * (if ∃ m ∈ M, job m = e ∧ ¬ dum m then 0 else 1) := by
      rw [← Finset.filter_filter, hLEv, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases h : ψ e = none
      · rw [if_pos h, if_neg (by rw [hcov]; exact not_not.mpr h)]; ring
      · rw [if_neg h, if_pos (by rw [hcov]; exact h)]; ring
    have hrm : ∀ e, ∑ o ∈ univ.filter (fun o : Op E 𝒞 Ks Dp => job o = e ∧ ¬ dum o), xx XL Dp o =
        ∑ c, ∑ i, ∑ j, XL e c i j := fun e => rmass_eq XL e
    simp only [hrm] at h3
    rw [hlhs, hLEv]
    have hWv : ∑ e ∈ LEs P G.ends v, G.w e ≤ n := by
      refine le_trans ?_ (hW v)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he; simp only [LEs, Finset.mem_filter, Finset.mem_univ, true_and] at he
        simp only [WGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and]; exact he.2
      · intro e _ _; exact (G.w_pos e).le
    have hW0 : 0 ≤ ∑ e ∈ LEs P G.ends v, G.w e := Finset.sum_nonneg (fun e _ => (G.w_pos e).le)
    have hε1 : ε' * ∑ e ∈ LEs P G.ends v, G.w e ≤ ε / 2 * n :=
      mul_le_mul hε'2 hWv hW0 (by linarith)
    have hm0 : (0 : ℝ) ≤ (LEs P G.ends v).card := Nat.cast_nonneg _
    have hm : ((LEs P G.ends v).card : ℝ) ≤ T ^ 2 / β := by rw [hTsq]; exact hLEs v
    have herr := err_arith cp β ε T L ((LEs P G.ends v).card) hcp0 hβ0 hε hT1 hL0 B hB0 hLB hm0 hm
      (by linarith) (by linarith)
    rw [hTsq] at herr
    have hX0 : 0 ≤ Real.sqrt ((LEs P G.ends v).card * L) + L := add_nonneg (Real.sqrt_nonneg _) hL0
    have hc2 : c₂ * (Real.sqrt ((LEs P G.ends v).card * L) + L) ≤
        cp * (Real.sqrt ((LEs P G.ends v).card * L) + L) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    simp only [zero_mul, add_zero]
    linarith

end SecMain
