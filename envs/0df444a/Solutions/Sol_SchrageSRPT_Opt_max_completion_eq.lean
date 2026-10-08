-- Prove2me | solution 1 for SchrageSRPT.Opt.max_completion_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:42:50.007313+00:00
-- url     : https://prove2.me/submissions/48c42a7f-86fd-4b55-a994-5eaebaef1fed

import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model



namespace SchrageSRPT.Opt
open MeasureTheory

lemma sch_intInt {A : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (δ n) volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun' (h.2.1 n).aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun x => ?_)
  rcases h.1 n x with h0 | h0 <;> simp [h0]

lemma sch_nonneg {A : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) (x : ℝ) : 0 ≤ δ n x := by
  rcases h.1 n x with h0 | h0 <;> simp [h0]

lemma sch_mono {A : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    (∫ t in (A n)..x, δ n t) ≤ ∫ t in (A n)..y, δ n t := by
  have : (∫ t in (A n)..y, δ n t) - ∫ t in (A n)..x, δ n t = ∫ t in x..y, δ n t :=
    intervalIntegral.integral_interval_sub_left (sch_intInt h n _ _) (sch_intInt h n _ _)
  have h2 : 0 ≤ ∫ t in x..y, δ n t :=
    intervalIntegral.integral_nonneg hxy (fun t _ => sch_nonneg h n t)
  linarith

lemma sch_cont {A : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) :
    Continuous (fun x => ∫ t in (A n)..x, δ n t) :=
  intervalIntegral.continuous_primitive (fun a b => sch_intInt h n a b) _

lemma sch_closed {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) :
    IsClosed (completedBy A P δ n) := by
  have : completedBy A P δ n = Set.Ici (A n) ∩ {x | P n ≤ ∫ t in (A n)..x, δ n t} := by
    ext x; simp [completedBy]
  rw [this]
  exact isClosed_Ici.inter (isClosed_le continuous_const (sch_cont h n))

lemma sch_sInf_mem {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ)
    (hne : (completedBy A P δ n).Nonempty) : sInf (completedBy A P δ n) ∈ completedBy A P δ n := by
  apply (sch_closed h n).csInf_mem hne
  refine ⟨A n, fun x hx => hx.1⟩

lemma sch_comp_ge {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) :
    ((A n : ℝ) : WithTop ℝ) ≤ completion A P δ n := by
  unfold completion
  split_ifs with hne
  · exact WithTop.coe_le_coe.2 (sch_sInf_mem h n hne).1
  · exact le_top

lemma sch_mem_inSystem {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) (y : ℝ) :
    n ∈ inSystem A P δ y ↔ A n ≤ y ∧ (y : WithTop ℝ) < completion A P δ n := by
  unfold inSystem
  simp only [Set.mem_setOf_eq, remaining]
  constructor
  · rintro ⟨hA, hr⟩
    refine ⟨hA, ?_⟩
    unfold completion
    split_ifs with hne
    · have hm := sch_sInf_mem h n hne
      have hle : y ≤ sInf (completedBy A P δ n) := by
        by_contra hlt
        push_neg at hlt
        have := sch_mono h n hlt.le
        linarith [hm.2]
      have hne' : y ≠ sInf (completedBy A P δ n) := by
        intro he; rw [← he] at hm; linarith [hm.2]
      exact WithTop.coe_lt_coe.2 (lt_of_le_of_ne hle hne')
    · exact WithTop.coe_lt_top _
  · rintro ⟨hA, hc⟩
    refine ⟨hA, ?_⟩
    unfold completion at hc
    split_ifs at hc with hne
    · have hc' := WithTop.coe_lt_coe.1 hc
      by_contra hr
      push_neg at hr
      have : y ∈ completedBy A P δ n := ⟨hA, by linarith⟩
      have := csInf_le ⟨A n, fun x hx => hx.1⟩ this
      linarith
    · by_contra hr
      push_neg at hr
      exact hne ⟨y, hA, by linarith⟩

lemma sch_comp_le_iff {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) (z : ℝ) :
    completion A P δ n ≤ (z : WithTop ℝ) ↔ A n ≤ z ∧ P n ≤ ∫ t in (A n)..z, δ n t := by
  unfold completion
  split_ifs with hne
  · rw [WithTop.coe_le_coe]
    constructor
    · intro hle
      have hm := sch_sInf_mem h n hne
      exact ⟨hm.1.trans hle, hm.2.trans (sch_mono h n hle)⟩
    · rintro ⟨h1, h2⟩
      exact csInf_le ⟨A n, fun x hx => hx.1⟩ ⟨h1, h2⟩
  · constructor
    · intro hle; exact absurd hle (by simp)
    · rintro ⟨h1, h2⟩; exact absurd ⟨z, h1, h2⟩ hne

lemma sch_comp_ext {a b : WithTop ℝ} (h : ∀ z : ℝ, a ≤ (z : WithTop ℝ) ↔ b ≤ (z : WithTop ℝ)) : a = b := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => rfl
    | coe b => exact absurd ((h b).2 le_rfl) (by simp)
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd ((h a).1 le_rfl) (by simp)
    | coe b =>
      congr 1
      have h1 := (h a).1 le_rfl
      have h2 := (h b).2 le_rfl
      exact le_antisymm (WithTop.coe_le_coe.1 h2) (WithTop.coe_le_coe.1 h1)

lemma sch_F_agree {A : ℕ → ℝ} {δ δ' : ℕ → ℝ → ℝ} (n : ℕ) (t : ℝ) (hAt : A n ≤ t)
    (hb : ∀ x, x < t → δ' n x = δ n x) :
    (∫ s in (A n)..t, δ' n s) = ∫ s in (A n)..t, δ n s := by
  apply intervalIntegral.integral_congr_ae
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({t} : Set ℝ) :=
    (Set.countable_singleton t).ae_notMem volume
  filter_upwards [hae] with x hx hxI
  rw [Set.uIoc_of_le hAt] at hxI
  have hxne : x ≠ t := by simpa using hx
  exact hb x (lt_of_le_of_ne hxI.2 hxne)

lemma sch_F_split {A : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) (t z : ℝ) :
    (∫ s in (A n)..z, δ n s) = (∫ s in (A n)..t, δ n s) + ∫ s in t..z, δ n s :=
  (intervalIntegral.integral_add_adjacent_intervals (sch_intInt h n _ _) (sch_intInt h n _ _)).symm


lemma sch_noover {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) (n : ℕ) (hP : 0 < P n)
    (hw : ∀ x, remaining A P δ n x ≤ 0 → δ n x = 0) (z : ℝ) (hz : A n ≤ z) :
    (∫ s in (A n)..z, δ n s) ≤ P n := by
  by_contra hcon
  push_neg at hcon
  have hzU : z ∈ completedBy A P δ n := ⟨hz, hcon.le⟩
  set x0 := sInf (completedBy A P δ n) with hx0
  have hm : x0 ∈ completedBy A P δ n := sch_sInf_mem h n ⟨z, hzU⟩
  have hx0z : x0 ≤ z := csInf_le ⟨A n, fun x hx => hx.1⟩ hzU
  have hF0 : (∫ s in (A n)..(A n), δ n s) = 0 := by simp
  obtain ⟨c, hc, hcF⟩ := intermediate_value_Icc hm.1 (sch_cont h n).continuousOn
    (show P n ∈ Set.Icc (∫ s in (A n)..(A n), δ n s) (∫ s in (A n)..x0, δ n s) from
      ⟨by rw [hF0]; exact hP.le, hm.2⟩)
  have hcU : c ∈ completedBy A P δ n := ⟨hc.1, by simp only at hcF; rw [hcF]⟩
  have hx0c : x0 ≤ c := csInf_le ⟨A n, fun x hx => hx.1⟩ hcU
  have hFx0 : (∫ s in (A n)..x0, δ n s) = P n := by
    have : x0 = c := le_antisymm hx0c hc.2
    rw [this]; exact hcF
  have hzero : (∫ s in x0..z, δ n s) = 0 := by
    have : (∫ s in x0..z, δ n s) = ∫ s in x0..z, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hx0z] at hx
      apply hw
      have := sch_mono h n hx.1
      simp only [remaining]
      linarith
    rw [this]; simp
  rw [sch_F_split h n x0 z, hzero, hFx0] at hcon
  linarith

lemma pair_iff {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) {j k : ℕ}
    (hPj : 0 < P j) (hPk : 0 < P k)
    (hwj : ∀ x, remaining A P δ j x ≤ 0 → δ j x = 0)
    (hwk : ∀ x, remaining A P δ k x ≤ 0 → δ k x = 0) (z : ℝ) :
    (completion A P δ j ≤ (z : WithTop ℝ) ∧ completion A P δ k ≤ (z : WithTop ℝ)) ↔
      (A j ≤ z ∧ A k ≤ z ∧ P j + P k ≤ (∫ s in (A j)..z, δ j s) + ∫ s in (A k)..z, δ k s) := by
  rw [sch_comp_le_iff h, sch_comp_le_iff h]
  constructor
  · rintro ⟨⟨a1, a2⟩, b1, b2⟩
    exact ⟨a1, b1, by linarith⟩
  · rintro ⟨a1, b1, c⟩
    have e1 := sch_noover h j hPj hwj z a1
    have e2 := sch_noover h k hPk hwk z b1
    exact ⟨⟨a1, by linarith⟩, b1, by linarith⟩

theorem maxcomp_core (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hwaste_o : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δo i x ≤ 0 → δo i x = 0)
    (hwaste_r : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δr i x ≤ 0 → δr i x = 0) :
    max (completion A P δo k) (completion A P δo j) =
      max (completion A P δr k) (completion A P δr j) := by
  have hAj : A j ≤ t := hj.1
  have hAk : A k ≤ t := hk.1
  have hj2 := hj.2
  have hk2 := hk.2
  simp only [remaining] at hj2 hk2
  have hFj0 : 0 ≤ ∫ s in (A j)..t, δo j s :=
    intervalIntegral.integral_nonneg hAj (fun x _ => sch_nonneg hδo j x)
  have hFk0 : 0 ≤ ∫ s in (A k)..t, δo k s :=
    intervalIntegral.integral_nonneg hAk (fun x _ => sch_nonneg hδo k x)
  have hPj : 0 < P j := by linarith
  have hPk : 0 < P k := by linarith
  have hagj := sch_F_agree (δ := δo) (δ' := δr) j t hAj (fun x hx => (hbefore x hx).1)
  have hagk := sch_F_agree (δ := δo) (δ' := δr) k t hAk (fun x hx => (hbefore x hx).2)
  apply sch_comp_ext
  intro z
  rw [max_le_iff, max_le_iff, and_comm (a := completion A P δo k ≤ _), and_comm (a := completion A P δr k ≤ _)]
  rw [pair_iff hδo hPj hPk (hwaste_o j (Or.inl rfl)) (hwaste_o k (Or.inr rfl)),
    pair_iff hδr hPj hPk (hwaste_r j (Or.inl rfl)) (hwaste_r k (Or.inr rfl))]
  by_cases hz : t ≤ z
  · have hsumz : (∫ s in t..z, δr j s) + (∫ s in t..z, δr k s) =
        (∫ s in t..z, δo j s) + ∫ s in t..z, δo k s := by
      rw [← intervalIntegral.integral_add (sch_intInt hδr j _ _) (sch_intInt hδr k _ _),
        ← intervalIntegral.integral_add (sch_intInt hδo j _ _) (sch_intInt hδo k _ _)]
      exact intervalIntegral.integral_congr (fun x _ => hsum x)
    rw [sch_F_split hδo j t z, sch_F_split hδo k t z, sch_F_split hδr j t z,
      sch_F_split hδr k t z, hagj, hagk]
    constructor
    · rintro ⟨a1, a2, a3⟩; exact ⟨a1, a2, by linarith⟩
    · rintro ⟨a1, a2, a3⟩; exact ⟨a1, a2, by linarith⟩
  · push_neg at hz
    have mj := sch_mono hδo j hz.le
    have mk := sch_mono hδo k hz.le
    have mj' := sch_mono hδr j hz.le
    have mk' := sch_mono hδr k hz.le
    constructor
    · rintro ⟨a1, a2, a3⟩; linarith
    · rintro ⟨a1, a2, a3⟩; linarith

end SchrageSRPT.Opt

open SchrageSRPT.Opt


theorem solution (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hwaste_o : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δo i x ≤ 0 → δo i x = 0)
    (hwaste_r : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δr i x ≤ 0 → δr i x = 0) :
    max (completion A P δo k) (completion A P δo j) =
      max (completion A P δr k) (completion A P δr j) := by
  exact maxcomp_core A P δo δr hδo hδr j k t hjk hj hk hbefore hsum hwaste_o hwaste_r
