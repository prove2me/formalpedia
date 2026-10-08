-- Prove2me | solution 1 for SchrageSRPT.Opt.srpt_reassign_min_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:41:10.449245+00:00
-- url     : https://prove2.me/submissions/ef5e0005-9589-43b4-a24d-9f773403d456

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

lemma sch_pair_le {A : ℕ → ℝ} {δ : ℕ → ℝ → ℝ} (h : IsSchedule A δ) {j k : ℕ} (hjk : j ≠ k) (x : ℝ) :
    δ j x + δ k x = 0 ∨ δ j x + δ k x = 1 := by
  rcases h.1 j x with h1 | h1 <;> rcases h.1 k x with h2 | h2
  · left; simp [h1, h2]
  · right; simp [h1, h2]
  · right; simp [h1, h2]
  · exact absurd (h.2.2.2 x j k h1 h2) hjk

lemma srpt_lt {A P : ℕ → ℝ} {δo : ℕ → ℝ → ℝ} {j k : ℕ} {t x : ℝ} (n : ℕ) (hx : x < t) :
    srptReassign A P δo j k t n x = δo n x := by
  simp [srptReassign, hx]

lemma srpt_j {A P : ℕ → ℝ} {δo : ℕ → ℝ → ℝ} {j k : ℕ} {t x : ℝ} (hx : t ≤ x) :
    srptReassign A P δo j k t j x =
      (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0) := by
  simp [srptReassign, not_lt.2 hx]

lemma srpt_k {A P : ℕ → ℝ} {δo : ℕ → ℝ → ℝ} {j k : ℕ} {t x : ℝ} (hjk : j ≠ k) (hx : t ≤ x) :
    srptReassign A P δo j k t k x = (δo j x + δo k x) -
      (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0) := by
  simp [srptReassign, not_lt.2 hx, hjk.symm]

lemma srpt_o {A P : ℕ → ℝ} {δo : ℕ → ℝ → ℝ} {j k : ℕ} {t x : ℝ} (n : ℕ) (hnj : n ≠ j) (hnk : n ≠ k)
    (hx : t ≤ x) : srptReassign A P δo j k t n x = δo n x := by
  simp [srptReassign, not_lt.2 hx, hnj, hnk]

lemma isSchedule_srptReassign {A P : ℕ → ℝ} {δo : ℕ → ℝ → ℝ} (h : IsSchedule A δo) {j k : ℕ}
    (hjk : j ≠ k) (t : ℝ) (hAj : A j ≤ t) (hAk : A k ≤ t) :
    IsSchedule A (srptReassign A P δo j k t) := by
  have hw : ∀ x, δo j x + δo k x = 0 ∨ δo j x + δo k x = 1 := sch_pair_le h hjk
  have hWc : Continuous (fun x => ∫ y in t..x, (δo j y + δo k y)) :=
    intervalIntegral.continuous_primitive
      (fun a b => (sch_intInt h j a b).add (sch_intInt h k a b)) _
  have hmeas : ∀ S : ℝ, MeasurableSet {x : ℝ | (∫ y in t..x, (δo j y + δo k y)) < S} :=
    fun S => measurableSet_lt hWc.measurable measurable_const
  have hwm : Measurable (fun x => δo j x + δo k x) := (h.2.1 j).add (h.2.1 k)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n x
    by_cases h1 : x < t
    · rw [srpt_lt n h1]; exact h.1 n x
    · have h1' := not_lt.1 h1
      by_cases hnj : n = j
      · subst hnj; rw [srpt_j h1']
        split_ifs
        · exact hw x
        · left; rfl
      · by_cases hnk : n = k
        · subst hnk; rw [srpt_k hjk h1']
          split_ifs
          · left; ring
          · simpa using hw x
        · rw [srpt_o n hnj hnk h1']; exact h.1 n x
  · intro n
    have : srptReassign A P δo j k t n = fun x => if x < t then δo n x else
        (if n = j then (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0)
         else if n = k then (δo j x + δo k x) -
           (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0)
         else δo n x) := by
      funext x
      by_cases h1 : x < t
      · simp [h1, srpt_lt n h1]
      · have h1' := not_lt.1 h1
        simp only [h1, if_false]
        by_cases hnj : n = j
        · subst hnj; simp [srpt_j h1']
        · by_cases hnk : n = k
          · subst hnk; simp [srpt_k hjk h1', hnj]
          · simp [srpt_o n hnj hnk h1', hnj, hnk]
    rw [this]
    refine Measurable.ite measurableSet_Iio (h.2.1 n) ?_
    by_cases hn : n = j
    · simp only [hn, if_true]
      exact Measurable.ite (hmeas _) hwm measurable_const
    · by_cases hn2 : n = k
      · simp only [hn, hn2, hjk.symm, if_false, if_true]
        exact hwm.sub (Measurable.ite (hmeas _) hwm measurable_const)
      · simp only [hn, hn2, if_false]
        exact h.2.1 n
  · intro n x hx
    by_cases h1 : x < t
    · rw [srpt_lt n h1]; exact h.2.2.1 n x hx
    · have h1' := not_lt.1 h1
      by_cases hnj : n = j
      · subst hnj; exfalso; linarith
      · by_cases hnk : n = k
        · subst hnk; exfalso; linarith
        · rw [srpt_o n hnj hnk h1']; exact h.2.2.1 n x hx
  · intro x n m hn hm
    have key : ∀ n, srptReassign A P δo j k t n x = 1 → (x < t ∧ δo n x = 1) ∨
        (t ≤ x ∧ n = j ∧ (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t ∧ δo j x + δo k x = 1) ∨
        (t ≤ x ∧ n = k ∧ ¬ (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t ∧ δo j x + δo k x = 1) ∨
        (t ≤ x ∧ n ≠ j ∧ n ≠ k ∧ δo n x = 1) := by
      intro n hn
      by_cases h1 : x < t
      · left; rw [srpt_lt n h1] at hn; exact ⟨h1, hn⟩
      · have h1' := not_lt.1 h1
        by_cases hnj : n = j
        · subst hnj; rw [srpt_j h1'] at hn
          right; left
          by_cases hc : (∫ y in t..x, (δo n y + δo k y)) < remaining A P δo n t
          · simp only [hc, if_true] at hn; exact ⟨h1', rfl, hc, hn⟩
          · simp only [hc, if_false] at hn; norm_num at hn
        · by_cases hnk : n = k
          · subst hnk; rw [srpt_k hjk h1'] at hn
            right; right; left
            by_cases hc : (∫ y in t..x, (δo j y + δo n y)) < remaining A P δo j t
            · simp only [hc, if_true] at hn; norm_num at hn
            · simp only [hc, if_false] at hn; exact ⟨h1', rfl, hc, by linarith⟩
          · rw [srpt_o n hnj hnk h1'] at hn
            right; right; right; exact ⟨h1', hnj, hnk, hn⟩
    have hjkx : ¬ (δo j x = 1 ∧ δo k x = 1) := fun ⟨a, b⟩ => hjk (h.2.2.2 x j k a b)
    have hcase : δo j x + δo k x = 1 → δo j x = 1 ∨ δo k x = 1 := by
      intro hs
      rcases h.1 j x with e | e <;> rcases h.1 k x with f | f
      · rw [e, f] at hs; norm_num at hs
      · right; exact f
      · left; exact e
      · rw [e, f] at hs; norm_num at hs
    have hexcl : ∀ a b, δo a x = 1 → δo b x = 1 → a = b := fun a b e f => h.2.2.2 x a b e f
    have other_clash : ∀ q, δo q x = 1 → q ≠ j → q ≠ k → δo j x + δo k x = 1 → False := by
      intro q hq hqj hqk hs
      rcases hcase hs with e | e
      · exact hqj (hexcl _ _ hq e)
      · exact hqk (hexcl _ _ hq e)
    rcases key n hn with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ <;>
    rcases key m hm with ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩
    all_goals first
      | exact h.2.2.2 x n m a2 b2
      | (exfalso; linarith)
      | (rw [a2, b2])
      | (exfalso; exact b3 a3)
      | (exfalso; exact a3 b3)
      | exact h.2.2.2 x n m a4 b4
      | (exfalso; exact other_clash n a4 a2 a3 b4)
      | (exfalso; exact other_clash m b4 b2 b3 a4)

lemma recv_bound {A P : ℕ → ℝ} {δo δr : ℕ → ℝ → ℝ} (hδo : IsSchedule A δo) (hδr : IsSchedule A δr)
    {i : ℕ} {t : ℝ} (hi : i ∈ inSystem A P δo t) (w : ℝ → ℝ)
    (hwint : ∀ a b, IntervalIntegrable w volume a b)
    (hb : ∀ x, x < t → δr i x = δo i x) (hle : ∀ x, δr i x ≤ w x) (m : ℝ)
    (hm : completion A P δr i ≤ (m : WithTop ℝ)) :
    t ≤ m ∧ remaining A P δo i t ≤ ∫ s in t..m, w s := by
  have hAi : A i ≤ t := hi.1
  have hpos : 0 < remaining A P δo i t := hi.2
  simp only [remaining] at hpos ⊢
  obtain ⟨h1, h2⟩ := (sch_comp_le_iff hδr i m).1 hm
  have hag := sch_F_agree (δ := δo) (δ' := δr) i t hAi hb
  have htm : t ≤ m := by
    by_contra hlt
    push_neg at hlt
    have := sch_mono hδr i hlt.le
    linarith
  refine ⟨htm, ?_⟩
  rw [sch_F_split hδr i t m, hag] at h2
  have : (∫ s in t..m, δr i s) ≤ ∫ s in t..m, w s :=
    intervalIntegral.integral_mono_on htm (sch_intInt hδr i _ _) (hwint _ _) (fun x _ => hle x)
  linarith

theorem reassign_core (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hS : remaining A P δo j t < remaining A P δo k t) (m : ℝ)
    (hm : min (completion A P δr k) (completion A P δr j) ≤ (m : WithTop ℝ)) :
    ∃ T : ℝ, T ≤ m ∧ completion A P (srptReassign A P δo j k t) j ≤ (T : WithTop ℝ) ∧
      (∫ y in t..T, (δo j y + δo k y)) ≤ remaining A P δo j t := by
  have hAj : A j ≤ t := hj.1
  have hAk : A k ≤ t := hk.1
  have hδs := isSchedule_srptReassign (P := P) hδo hjk t hAj hAk
  have hwint : ∀ a b, IntervalIntegrable (fun y => δo j y + δo k y) volume a b :=
    fun a b => (sch_intInt hδo j a b).add (sch_intInt hδo k a b)
  have hWc : Continuous (fun x => ∫ y in t..x, (δo j y + δo k y)) :=
    intervalIntegral.continuous_primitive hwint _
  have hSpos : 0 < remaining A P δo j t := hj.2
  have hSm : t ≤ m ∧ remaining A P δo j t ≤ ∫ s in t..m, (δo j s + δo k s) := by
    rcases min_le_iff.1 hm with h | h
    · have := recv_bound hδo hδr hk (fun y => δo j y + δo k y) hwint (fun x hx => (hbefore x hx).2)
        (fun x => by have := hsum x; have := sch_nonneg hδr j x; linarith) m h
      exact ⟨this.1, by linarith [this.2]⟩
    · exact recv_bound hδo hδr hj (fun y => δo j y + δo k y) hwint (fun x hx => (hbefore x hx).1)
        (fun x => by have := hsum x; have := sch_nonneg hδr k x; linarith) m h
  set S := remaining A P δo j t with hSdef
  set W : ℝ → ℝ := fun x => ∫ y in t..x, (δo j y + δo k y) with hW
  set U : Set ℝ := {z | t ≤ z ∧ S ≤ W z} with hU
  have hUc : IsClosed U := isClosed_Ici.inter (isClosed_le continuous_const hWc)
  have hUne : U.Nonempty := ⟨m, hSm⟩
  have hUb : BddBelow U := ⟨t, fun x hx => hx.1⟩
  set T := sInf U with hT
  have hTU : T ∈ U := hUc.csInf_mem hUne hUb
  have hTm : T ≤ m := csInf_le hUb hSm
  have hWT : W T ≤ S := by
    rcases eq_or_lt_of_le hTU.1 with h0 | h0
    · rw [← h0]; simp [hW]; exact hSpos.le
    · by_contra hcon
      push_neg at hcon
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
        ((hWc.continuousAt (x := T)).eventually (lt_mem_nhds hcon))
      set x := max (T - ε / 2) t with hx
      have hxT : x < T := max_lt (by linarith) h0
      have hxd : dist x T < ε := by
        rw [Real.dist_eq, abs_lt]
        constructor
        · have : T - ε / 2 ≤ x := le_max_left _ _
          linarith
        · linarith
      have hxU : x ∈ U := ⟨le_max_right _ _, (hball hxd).le⟩
      have := csInf_le hUb hxU
      linarith
  refine ⟨T, hTm, ?_, hWT⟩
  rw [sch_comp_le_iff hδs]
  refine ⟨hAj.trans hTU.1, ?_⟩
  have hFt : (∫ s in (A j)..t, srptReassign A P δo j k t j s) = ∫ s in (A j)..t, δo j s :=
    sch_F_agree (δ := δo) (δ' := srptReassign A P δo j k t) j t hAj (fun x hx => srpt_lt j hx)
  have hint : (∫ s in t..T, srptReassign A P δo j k t j s) = W T := by
    apply intervalIntegral.integral_congr_ae
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({T} : Set ℝ) :=
      (Set.countable_singleton T).ae_notMem volume
    filter_upwards [hae] with x hx hxI
    rw [Set.uIoc_of_le hTU.1] at hxI
    have hxne : x ≠ T := by simpa using hx
    have hxT : x < T := lt_of_le_of_ne hxI.2 hxne
    rw [srpt_j hxI.1.le]
    have : W x < S := by
      by_contra hcon
      push_neg at hcon
      have := csInf_le hUb (show x ∈ U from ⟨hxI.1.le, hcon⟩)
      linarith
    have this' : (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t := this
    rw [if_pos this']
  rw [sch_F_split hδs j t T, hFt, hint]
  have := hTU.2
  simp only [hSdef, remaining] at this ⊢
  linarith

theorem reassign_le_core (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hS : remaining A P δo j t < remaining A P δo k t) :
    min (completion A P (srptReassign A P δo j k t) k)
        (completion A P (srptReassign A P δo j k t) j) ≤
      min (completion A P δr k) (completion A P δr j) := by
  by_cases htop : min (completion A P δr k) (completion A P δr j) = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 htop
    obtain ⟨T, hTm, hT, _⟩ := reassign_core A P δo δr hδo hδr j k t hjk hj hk hbefore hsum hS m hm.ge
    rw [← hm]
    exact (min_le_right _ _).trans (hT.trans (WithTop.coe_le_coe.2 hTm))

theorem reassign_lt_core (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j k : ℕ) (t v : ℝ) (hv : 0 < v) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hk_served : ∀ x ∈ Set.Icc t (t + v), δo k x = 1)
    (hS : remaining A P δo j t < remaining A P δo k t)
    (hfinite : min (completion A P δo k) (completion A P δo j) ≠ ⊤) :
    min (completion A P (srptReassign A P δo j k t) k)
        (completion A P (srptReassign A P δo j k t) j) <
      min (completion A P δo k) (completion A P δo j) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hfinite
  obtain ⟨T, hTm, hT, hWT⟩ := reassign_core A P δo δo hδo hδo j k t hjk hj hk
    (fun x _ => ⟨rfl, rfl⟩) (fun x => rfl) hS m hm.ge
  have hAj : A j ≤ t := hj.1
  have hAk : A k ≤ t := hk.1
  have hwint : ∀ a b, IntervalIntegrable (fun y => δo j y + δo k y) volume a b :=
    fun a b => (sch_intInt hδo j a b).add (sch_intInt hδo k a b)
  -- W m > S_j
  have hWm : remaining A P δo j t < ∫ y in t..m, (δo j y + δo k y) := by
    have hsplit : (∫ y in t..m, (δo j y + δo k y)) = (∫ y in t..m, δo j y) + ∫ y in t..m, δo k y :=
      intervalIntegral.integral_add (sch_intInt hδo j _ _) (sch_intInt hδo k _ _)
    rw [hsplit]
    rcases min_choice (completion A P δo k) (completion A P δo j) with hc | hc
    · -- k attains the min
      rw [hc] at hm
      have hkm : completion A P δo k ≤ (m : WithTop ℝ) := hm.ge
      obtain ⟨h1, h2⟩ := (sch_comp_le_iff hδo k m).1 hkm
      have htm : t ≤ m := by
        by_contra hlt
        push_neg at hlt
        have := sch_mono hδo k hlt.le
        have := hk.2
        simp only [remaining] at this
        linarith
      have h3 := sch_F_split hδo k t m
      have hk2 := hk.2
      simp only [remaining] at hk2 hS ⊢
      have h4 : 0 ≤ ∫ y in t..m, δo j y := intervalIntegral.integral_nonneg htm (fun x _ => sch_nonneg hδo j x)
      linarith
    · rw [hc] at hm
      have hjm : completion A P δo j ≤ (m : WithTop ℝ) := hm.ge
      obtain ⟨h1, h2⟩ := (sch_comp_le_iff hδo j m).1 hjm
      have htm' : (t : WithTop ℝ) < completion A P δo j := ((sch_mem_inSystem hδo j t).1 hj).2
      rw [← hm] at htm'
      have htm : t < m := WithTop.coe_lt_coe.1 htm'
      have h3 := sch_F_split hδo j t m
      have hj2 := hj.2
      simp only [remaining] at hj2 ⊢
      -- k's part is positive
      set e := min m (t + v) with he
      have het : t < e := lt_min htm (by linarith)
      have hk1 : e - t ≤ ∫ y in t..m, δo k y := by
        have e1 : (∫ y in t..e, δo k y) = e - t := by
          have : (∫ y in t..e, δo k y) = ∫ y in t..e, (1:ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le het.le] at hx
            exact hk_served x ⟨hx.1, hx.2.trans (min_le_right _ _)⟩
          rw [this]; simp
        have e2 : (∫ y in t..m, δo k y) = (∫ y in t..e, δo k y) + ∫ y in e..m, δo k y :=
          (intervalIntegral.integral_add_adjacent_intervals (sch_intInt hδo k _ _) (sch_intInt hδo k _ _)).symm
        have e3 : 0 ≤ ∫ y in e..m, δo k y :=
          intervalIntegral.integral_nonneg (min_le_left _ _) (fun x _ => sch_nonneg hδo k x)
        linarith
      linarith
  have hTlt : T < m := by
    rcases lt_or_eq_of_le hTm with h | h
    · exact h
    · exfalso; rw [h] at hWT; linarith
  rw [← hm]
  exact lt_of_le_of_lt ((min_le_right _ _).trans hT) (WithTop.coe_lt_coe.2 hTlt)

end SchrageSRPT.Opt

open SchrageSRPT.Opt


theorem solution (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hS : remaining A P δo j t < remaining A P δo k t) :
    min (completion A P (srptReassign A P δo j k t) k)
        (completion A P (srptReassign A P δo j k t) j) ≤
      min (completion A P δr k) (completion A P δr j) := by
  exact reassign_le_core A P δo δr hδo hδr j k t hjk hj hk hbefore hsum hS
