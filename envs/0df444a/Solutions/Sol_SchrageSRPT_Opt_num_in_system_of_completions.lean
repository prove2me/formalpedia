-- Prove2me | solution 1 for SchrageSRPT.Opt.num_in_system_of_completions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:31:53.651114+00:00
-- url     : https://prove2.me/submissions/8a874722-4f44-4202-93cb-cf8490ee187f

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


open Classical in
lemma sch_ncard_jk {S : Set ℕ} (hS : S.Finite) {j k : ℕ} (hjk : j ≠ k) :
    S.ncard = (S \ {j, k}).ncard + (if j ∈ S then 1 else 0) + (if k ∈ S then 1 else 0) := by
  have e : S \ {j, k} = (S \ {j}) \ {k} := by ext x; simp; tauto
  rw [e]
  have h1 : ((S \ {j}) \ {k}).ncard + (if k ∈ S \ {j} then 1 else 0) = (S \ {j}).ncard := by
    split_ifs with h
    · exact Set.ncard_diff_singleton_add_one h (hS.subset Set.diff_subset)
    · rw [Set.diff_singleton_eq_self h]; simp
  have h2 : (S \ {j}).ncard + (if j ∈ S then 1 else 0) = S.ncard := by
    split_ifs with h
    · exact Set.ncard_diff_singleton_add_one h hS
    · rw [Set.diff_singleton_eq_self h]; simp
  have h3 : (if k ∈ S \ {j} then 1 else 0) = (if k ∈ S then 1 else 0) := by
    simp [Set.mem_diff, hjk.symm]
  omega

open Classical in
theorem nis_core (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {n | A n ≤ t}.Finite)
    (δo δr : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo) (hδr : IsSchedule A δr)
    (j k : ℕ) (hjk : j ≠ k)
    (h1 : ∀ i, i ≠ j → i ≠ k → completion A P δo i = completion A P δr i)
    (h2 : min (completion A P δr k) (completion A P δr j) <
      min (completion A P δo k) (completion A P δo j))
    (h3 : max (completion A P δr k) (completion A P δr j) =
      max (completion A P δo k) (completion A P δo j))
    (hjr : completion A P δr j ≤ completion A P δr k) :
    ∀ y : ℝ,
      (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j) →
        numInSystem A P δr y + 1 = numInSystem A P δo y) ∧
      (¬ (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j)) →
        numInSystem A P δr y = numInSystem A P δo y) := by
  intro y
  have fin : ∀ δ : ℕ → ℝ → ℝ, IsSchedule A δ → (inSystem A P δ y).Finite := by
    intro δ hδ
    refine (hfin y).subset ?_
    intro n hn; exact hn.1
  have hB : inSystem A P δr y \ {j, k} = inSystem A P δo y \ {j, k} := by
    ext i
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨hi, hij, hik⟩
      refine ⟨?_, hij, hik⟩
      rw [sch_mem_inSystem hδo, h1 i hij hik]
      exact (sch_mem_inSystem hδr i y).1 hi
    · rintro ⟨hi, hij, hik⟩
      refine ⟨?_, hij, hik⟩
      rw [sch_mem_inSystem hδr, ← h1 i hij hik]
      exact (sch_mem_inSystem hδo i y).1 hi
  unfold numInSystem
  rw [sch_ncard_jk (fin δr hδr) hjk, sch_ncard_jk (fin δo hδo) hjk, hB]
  simp only [sch_mem_inSystem hδr, sch_mem_inSystem hδo]
  have gj := sch_comp_ge (P := P) hδr j
  have gk := sch_comp_ge (P := P) hδr k
  have gjo := sch_comp_ge (P := P) hδo j
  have gko := sch_comp_ge (P := P) hδo k
  have hminr : min (completion A P δr k) (completion A P δr j) = completion A P δr j :=
    min_eq_right hjr
  have hmaxr : max (completion A P δr k) (completion A P δr j) = completion A P δr k := max_eq_left hjr
  rw [hminr] at h2
  rw [hmaxr] at h3
  generalize completion A P δr j = c at *
  generalize completion A P δr k = d at *
  generalize completion A P δo j = cj at *
  generalize completion A P δo k = ck at *
  have hmM : min ck cj ≤ max ck cj := min_le_max
  -- facts
  have cfin : ∀ (z : WithTop ℝ) (a : ℝ), (a : WithTop ℝ) ≤ z → z ≤ (y : WithTop ℝ) → a ≤ y := by
    intro z a h1 h2; exact WithTop.coe_le_coe.1 (h1.trans h2)
  constructor
  · rintro ⟨hcy, hym⟩
    have hy1 : (y : WithTop ℝ) < ck := lt_of_lt_of_le hym (min_le_left _ _)
    have hy2 : (y : WithTop ℝ) < cj := lt_of_lt_of_le hym (min_le_right _ _)
    have hy3 : (y : WithTop ℝ) < d := by
      rw [h3]; exact lt_of_lt_of_le hym hmM
    have hAj : A j ≤ y := cfin c _ gj hcy
    have hcj : ¬ (y : WithTop ℝ) < c := not_lt.2 hcy
    simp [hAj, hy1, hy2, hy3, hcj]
    split_ifs <;> omega
  · intro hn
    by_cases hc : (y : WithTop ℝ) < c
    · have hy1 : (y : WithTop ℝ) < ck := lt_of_lt_of_le hc (h2.le.trans (min_le_left _ _))
      have hy2 : (y : WithTop ℝ) < cj := lt_of_lt_of_le hc (h2.le.trans (min_le_right _ _))
      have hy3 : (y : WithTop ℝ) < d := lt_of_lt_of_le hc hjr
      simp [hc, hy1, hy2, hy3]
    · have hcy : c ≤ (y : WithTop ℝ) := not_lt.1 hc
      have hym : ¬ (y : WithTop ℝ) < min ck cj := fun h => hn ⟨hcy, h⟩
      have hmy : min ck cj ≤ (y : WithTop ℝ) := not_lt.1 hym
      have hAj : A j ≤ y := cfin c _ gj hcy
      -- c < min ≤ y
      simp only [hc, and_false, if_false]
      by_cases hd : (y : WithTop ℝ) < d
      · rcases le_total ck cj with hle | hle
        · have hmin : min ck cj = ck := min_eq_left hle
          have hmax : max ck cj = cj := max_eq_right hle
          rw [hmax] at h3
          rw [hmin] at hmy
          have hck : ¬ (y : WithTop ℝ) < ck := not_lt.2 hmy
          have hAk : A k ≤ y := cfin ck _ gko hmy
          have hyj : (y : WithTop ℝ) < cj := h3 ▸ hd
          simp [hck, hAj, hAk, hd, hyj]
        · have hmin : min ck cj = cj := min_eq_right hle
          have hmax : max ck cj = ck := max_eq_left hle
          rw [hmax] at h3
          rw [hmin] at hmy
          have hcj' : ¬ (y : WithTop ℝ) < cj := not_lt.2 hmy
          have hyk : (y : WithTop ℝ) < ck := h3 ▸ hd
          simp [hcj', hd, hyk]
      · have hd' : d ≤ (y : WithTop ℝ) := not_lt.1 hd
        have hmx : max ck cj ≤ (y : WithTop ℝ) := h3 ▸ hd'
        have hck : ¬ (y : WithTop ℝ) < ck := not_lt.2 ((le_max_left _ _).trans hmx)
        have hcj' : ¬ (y : WithTop ℝ) < cj := not_lt.2 ((le_max_right _ _).trans hmx)
        simp [hck, hcj', hd]

end SchrageSRPT.Opt

open SchrageSRPT.Opt


theorem solution (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {n | A n ≤ t}.Finite)
    (δo δr : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo) (hδr : IsSchedule A δr)
    (j k : ℕ) (hjk : j ≠ k)
    (h1 : ∀ i, i ≠ j → i ≠ k → completion A P δo i = completion A P δr i)
    (h2 : min (completion A P δr k) (completion A P δr j) <
      min (completion A P δo k) (completion A P δo j))
    (h3 : max (completion A P δr k) (completion A P δr j) =
      max (completion A P δo k) (completion A P δo j))
    (hjr : completion A P δr j ≤ completion A P δr k) :
    ∀ y : ℝ,
      (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j) →
        numInSystem A P δr y + 1 = numInSystem A P δo y) ∧
      (¬ (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j)) →
        numInSystem A P δr y = numInSystem A P δo y) := by
  exact nis_core A P hfin δo δr hδo hδr j k hjk h1 h2 h3 hjr
