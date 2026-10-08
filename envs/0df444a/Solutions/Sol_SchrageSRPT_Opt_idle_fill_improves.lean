-- Prove2me | solution 1 for SchrageSRPT.Opt.idle_fill_improves
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:35:34.653211+00:00
-- url     : https://prove2.me/submissions/d018ba96-760d-4ab3-90fa-7766ce6eb4f0

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

lemma isSchedule_idleFill {A : ℕ → ℝ} {δo : ℕ → ℝ → ℝ} (h : IsSchedule A δo) (j : ℕ) (t v : ℝ)
    (hj : A j ≤ t) : IsSchedule A (idleFill δo j t v) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n x; unfold idleFill
    split_ifs
    · right; rfl
    · left; rfl
    · exact h1 n x
  · intro n
    have hm : MeasurableSet {x : ℝ | t ≤ x ∧ x ≤ t + v} :=
      (measurableSet_Ici.inter measurableSet_Iic)
    unfold idleFill
    by_cases hn : n = j
    · simp only [hn, if_true]
      exact Measurable.ite hm measurable_const (h2 j)
    · simp only [hn, if_false]
      exact Measurable.ite hm measurable_const (h2 n)
  · intro n x hx; unfold idleFill
    split_ifs with hw hn
    · exfalso; subst hn; linarith [hw.1]
    · rfl
    · exact h3 n x hx
  · intro x n m hn hm; unfold idleFill at hn hm
    split_ifs at hn hm with hw hn' hm'
    · rw [hn', hm']
    · simp at hm
    · simp at hn
    · simp at hn
    · exact h4 x n m hn hm

lemma idle_other (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j : ℕ) (t v : ℝ) (hAj : A j ≤ t)
    (hb1 : ∀ x ∈ Set.Icc t (t + v), ∀ k ∈ inSystem A P δo x, δo k x = 0)
    (i : ℕ) (hij : i ≠ j) (z : ℝ) (hAz : A i ≤ z) :
    P i ≤ ∫ s in (A i)..z, idleFill δo j t v i s ↔ P i ≤ ∫ s in (A i)..z, δo i s := by
  have hδ' := isSchedule_idleFill hδo j t v hAj
  constructor
  · intro h
    refine h.trans ?_
    apply intervalIntegral.integral_mono_on hAz (sch_intInt hδ' i _ _) (sch_intInt hδo i _ _)
    intro x _
    unfold idleFill
    simp only [hij, if_false]
    split_ifs
    · exact sch_nonneg hδo i x
    · exact le_rfl
  · intro hP
    set S := completedBy A P δo i with hS
    have hne : S.Nonempty := ⟨z, hAz, hP⟩
    set x0 := sInf S with hx0
    have hm : x0 ∈ S := sch_sInf_mem hδo i hne
    have hx0z : x0 ≤ z := csInf_le ⟨A i, fun x hx => hx.1⟩ ⟨hAz, hP⟩
    have heq : (∫ s in (A i)..x0, idleFill δo j t v i s) = ∫ s in (A i)..x0, δo i s := by
      apply intervalIntegral.integral_congr_ae
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({x0} : Set ℝ) :=
        (Set.countable_singleton x0).ae_notMem volume
      filter_upwards [hae] with x hx hxI
      have hAx0 : A i ≤ x0 := hm.1
      rw [Set.uIoc_of_le hAx0] at hxI
      have hxne : x ≠ x0 := by simpa using hx
      have hxlt : x < x0 := lt_of_le_of_ne hxI.2 hxne
      have hxF : x ∉ S := by
        intro hxS
        have := csInf_le (⟨A i, fun x hx => hx.1⟩ : BddBelow S) hxS
        linarith
      unfold idleFill
      simp only [hij, if_false]
      split_ifs with hw
      · symm
        apply hb1 x ⟨hw.1, hw.2⟩ i
        refine ⟨hxI.1.le, ?_⟩
        simp only [remaining]
        by_contra hcon
        push_neg at hcon
        exact hxF ⟨hxI.1.le, by linarith⟩
      · rfl
    calc P i ≤ ∫ s in (A i)..x0, δo i s := hm.2
      _ = ∫ s in (A i)..x0, idleFill δo j t v i s := heq.symm
      _ ≤ ∫ s in (A i)..z, idleFill δo j t v i s := sch_mono hδ' i hx0z

theorem idle_core (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j : ℕ) (t v : ℝ) (hv : 0 < v) (hj : j ∈ inSystem A P δo t)
    (hj_idle : ∀ x ∈ Set.Icc t (t + v), δo j x = 0)
    (hb1 : ∀ x ∈ Set.Icc t (t + v), ∀ k ∈ inSystem A P δo x, δo k x = 0)
    (hCj : completion A P δo j ≠ ⊤) :
    completion A P (idleFill δo j t v) j < completion A P δo j ∧
      ∀ i, i ≠ j → completion A P (idleFill δo j t v) i = completion A P δo i := by
  have hAj : A j ≤ t := hj.1
  have hδ' := isSchedule_idleFill hδo j t v hAj
  constructor
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hCj
    rw [← hc]
    have htc : (t : WithTop ℝ) < completion A P δo j := ((sch_mem_inSystem hδo j t).1 hj).2
    rw [← hc] at htc
    have htc' : t < c := WithTop.coe_lt_coe.1 htc
    have hFc : P j ≤ ∫ s in (A j)..c, δo j s :=
      ((sch_comp_le_iff hδo j c).1 (by rw [← hc])).2
    -- decomposition
    set h : ℝ → ℝ := fun x => if t ≤ x ∧ x ≤ t + v then 1 else 0 with hh
    have hdecomp : ∀ x, idleFill δo j t v j x = δo j x + h x := by
      intro x
      simp only [idleFill, hh, if_true]
      split_ifs with hw
      · rw [hj_idle x ⟨hw.1, hw.2⟩]; simp
      · simp
    have hhint : ∀ a b, IntervalIntegrable h volume a b := by
      intro a b
      apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun'
      · have hm : MeasurableSet {x : ℝ | t ≤ x ∧ x ≤ t + v} :=
          (measurableSet_Ici.inter measurableSet_Iic)
        exact (Measurable.ite hm measurable_const measurable_const).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun x => ?_)
        simp only [hh]; split_ifs <;> simp
    have hh0 : ∀ x, 0 ≤ h x := by intro x; simp only [hh]; split_ifs <;> simp
    set w0 := min c (t + v) with hw0
    have hw0t : t < w0 := lt_min htc' (by linarith)
    have hint_lb : w0 - t ≤ ∫ s in (A j)..c, h s := by
      have e1 : (∫ s in t..w0, h s) = w0 - t := by
        have : (∫ s in t..w0, h s) = ∫ s in t..w0, (1:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le hw0t.le] at hx
          have : x ≤ t + v := hx.2.trans (min_le_right _ _)
          simp [hh, hx.1, this]
        rw [this]; simp
      have e2 : (∫ s in (A j)..w0, h s) = (∫ s in (A j)..t, h s) + ∫ s in t..w0, h s :=
        (intervalIntegral.integral_add_adjacent_intervals (hhint _ _) (hhint _ _)).symm
      have e3 : 0 ≤ ∫ s in (A j)..t, h s := intervalIntegral.integral_nonneg hAj (fun x _ => hh0 x)
      have e4 : (∫ s in (A j)..c, h s) = (∫ s in (A j)..w0, h s) + ∫ s in w0..c, h s :=
        (intervalIntegral.integral_add_adjacent_intervals (hhint _ _) (hhint _ _)).symm
      have e5 : 0 ≤ ∫ s in w0..c, h s :=
        intervalIntegral.integral_nonneg (min_le_left _ _) (fun x _ => hh0 x)
      linarith
    have hF'c : (∫ s in (A j)..c, idleFill δo j t v j s) = (∫ s in (A j)..c, δo j s) + ∫ s in (A j)..c, h s := by
      rw [← intervalIntegral.integral_add (sch_intInt hδo j _ _) (hhint _ _)]
      exact intervalIntegral.integral_congr (fun x _ => hdecomp x)
    have hlt : P j < ∫ s in (A j)..c, idleFill δo j t v j s := by
      rw [hF'c]; linarith
    have hcont := sch_cont hδ' j
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      ((hcont.continuousAt (x := c)).eventually (lt_mem_nhds hlt))
    set w := max (c - ε / 2) t with hw
    have hwc : w < c := max_lt (by linarith) htc'
    have hwt : t ≤ w := le_max_right _ _
    have hwd : dist w c < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have : c - ε / 2 ≤ w := le_max_left _ _
        linarith
      · linarith
    have hPw := hball hwd
    have : completion A P (idleFill δo j t v) j ≤ (w : WithTop ℝ) :=
      (sch_comp_le_iff hδ' j w).2 ⟨by linarith, hPw.le⟩
    exact lt_of_le_of_lt this (WithTop.coe_lt_coe.2 hwc)
  · intro i hij
    apply sch_comp_ext
    intro z
    rw [sch_comp_le_iff hδ', sch_comp_le_iff hδo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (idle_other A P δo hδo j t v hAj hb1 i hij z h1).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (idle_other A P δo hδo j t v hAj hb1 i hij z h1).2 h2⟩

end SchrageSRPT.Opt

open SchrageSRPT.Opt


theorem solution (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j : ℕ) (t v : ℝ) (hv : 0 < v) (hj : j ∈ inSystem A P δo t)
    (hj_idle : ∀ x ∈ Set.Icc t (t + v), δo j x = 0)
    (hb1 : ∀ x ∈ Set.Icc t (t + v), ∀ k ∈ inSystem A P δo x, δo k x = 0)
    (hCj : completion A P δo j ≠ ⊤) :
    completion A P (idleFill δo j t v) j < completion A P δo j ∧
      ∀ i, i ≠ j → completion A P (idleFill δo j t v) i = completion A P δo i := by
  exact idle_core A P δo hδo j t v hv hj hj_idle hb1 hCj
