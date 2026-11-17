-- Prove2me | solution 1 for StochLoadBal.Makespan.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:39:25.22255+00:00
-- url     : https://prove2.me/submissions/8e1dfb38-0c7b-4543-9508-263755a95813

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

lemma disjoint_blocks_prod_indep {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n r : ℕ} (Y : Fin n → Ω → ℝ) (hmeas : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y P) (f : Fin r → Finset (Fin n))
    (hdisj : Pairwise (fun a b => Disjoint (f a) (f b))) (θ : ℝ) (S : Finset (Fin r)) :
    P (⋂ a ∈ S, {ω | ∑ j ∈ f a, Y j ω < θ}) =
      ∏ a ∈ S, P {ω | ∑ j ∈ f a, Y j ω < θ} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S haS ih =>
    rw [Finset.prod_insert haS, ← ih, Finset.set_biInter_insert]
    set T : Finset (Fin n) := S.biUnion f with hT
    have hdisj_aT : Disjoint (f a) T := by
      rw [Finset.disjoint_left]
      intro j hja hjT
      rw [hT, Finset.mem_biUnion] at hjT
      obtain ⟨b, hbS, hjb⟩ := hjT
      have hab : a ≠ b := fun h => haS (h ▸ hbS)
      exact Finset.disjoint_left.mp (hdisj hab) hja hjb
    have hI := hind.indepFun_finset (f a) T hdisj_aT hmeas
    apply hI.meas_inter
    · refine ⟨{v | ∑ j, v j < θ}, ?_, ?_⟩
      · exact measurableSet_lt (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
          measurable_const
      · ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        rw [Finset.sum_coe_sort (f a) (fun j => Y j ω)]
    · let ext : (T → ℝ) → Fin n → ℝ := fun v j => if h : j ∈ T then v ⟨j, h⟩ else 0
      have hext : Measurable ext := by
        rw [measurable_pi_iff]
        intro j
        by_cases h : j ∈ T
        · simp only [ext, h, dite_true]; exact measurable_pi_apply _
        · simp only [ext, h, dite_false]; exact measurable_const
      refine ⟨{v | ∀ b ∈ S, ∑ j ∈ f b, ext v j < θ}, ?_, ?_⟩
      · have : {v : T → ℝ | ∀ b ∈ S, ∑ j ∈ f b, ext v j < θ} =
            ⋂ b ∈ S, {v | ∑ j ∈ f b, ext v j < θ} := by ext v; simp
        rw [this]
        refine Finset.measurableSet_biInter S (fun b _ => ?_)
        exact measurableSet_lt (Finset.measurable_sum _
          (fun j _ => (measurable_pi_apply j).comp hext)) measurable_const
      · ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iInter]
        apply forall₂_congr
        intro b hb
        have hsum : ∑ j ∈ f b, ext (fun i => Y (↑i) ω) j = ∑ j ∈ f b, Y j ω := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjT : j ∈ T := by rw [hT, Finset.mem_biUnion]; exact ⟨b, hb, hj⟩
          simp [ext, hjT]
        rw [hsum]

lemma exists_disjoint_blocks {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j ∧ w j ≤ 1) (M : ℝ) (hM : 0 < M) :
    ∃ (r : ℕ) (f : Fin r → Finset ι),
      (∀ a, f a ⊆ s) ∧
      Pairwise (fun a b => Disjoint (f a) (f b)) ∧
      (∀ a, M ≤ ∑ j ∈ f a, w j) ∧
      ∑ j ∈ s, w j ≤ (r : ℝ) * (M + 1) + M := by
  classical
  induction hcard : s.card using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases hlt : ∑ j ∈ s, w j < M
    · refine ⟨0, Fin.elim0, fun a => a.elim0, ?_, fun a => a.elim0, ?_⟩
      · intro a; exact a.elim0
      · simp; linarith
    · push_neg at hlt
      let P : Finset ι → Prop := fun t => t ⊆ s ∧ M ≤ ∑ j ∈ t, w j
      have hex : ∃ t, P t := ⟨s, Finset.Subset.rfl, hlt⟩
      obtain ⟨t, ⟨ht_sub, ht_sum⟩, ht_min⟩ :=
        @WellFounded.has_min (Finset ι) (fun a b => a.card < b.card)
          (measure Finset.card).wf {t | P t} hex
      have ht_ne : t.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.sum_empty] at ht_sum
        linarith
      obtain ⟨j₀, hj₀⟩ := ht_ne
      have h_erase_lt : ∑ j ∈ t.erase j₀, w j < M := by
        by_contra hge
        push_neg at hge
        have hP : P (t.erase j₀) := ⟨(Finset.erase_subset j₀ t).trans ht_sub, hge⟩
        exact ht_min (t.erase j₀) hP (Finset.card_erase_lt_of_mem hj₀)
      have ht_ub : ∑ j ∈ t, w j ≤ M + 1 := by
        rw [← Finset.add_sum_erase t w hj₀]
        have hj₀_le : w j₀ ≤ 1 := (hw j₀ (ht_sub hj₀)).2
        linarith
      have hrem_card : (s \ t).card < k := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.sdiff_ssubset ht_sub ⟨j₀, hj₀⟩)
      have hrem_w : ∀ j ∈ s \ t, 0 ≤ w j ∧ w j ≤ 1 := fun j hj =>
        hw j (Finset.sdiff_subset hj)
      obtain ⟨r', f', hf'_sub, hf'_disj, hf'_sum, hf'_rem⟩ :=
        ih (s \ t).card hrem_card (s \ t) hrem_w rfl
      refine ⟨r' + 1, Fin.cons t f', ?_, ?_, ?_, ?_⟩
      · intro a
        refine Fin.cases ht_sub (fun b => (hf'_sub b).trans Finset.sdiff_subset) a
      · intro a b hab
        induction a using Fin.cases with
        | zero =>
          induction b using Fin.cases with
          | zero => exact (hab rfl).elim
          | succ b =>
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact Finset.disjoint_of_subset_right (hf'_sub b) disjoint_sdiff_self_right
        | succ a =>
          induction b using Fin.cases with
          | zero =>
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact Finset.disjoint_of_subset_left (hf'_sub a) disjoint_sdiff_self_left
          | succ b =>
            simp only [Fin.cons_succ]
            exact hf'_disj (fun h => hab (congrArg Fin.succ h))
      · intro a
        refine Fin.cases ht_sum hf'_sum a
      · have hsplit : ∑ j ∈ s, w j = ∑ j ∈ t, w j + ∑ j ∈ s \ t, w j := by
          rw [← Finset.sum_sdiff ht_sub, add_comm]
        push_cast
        linarith

lemma integrable_exp_mul {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : ℝ) (hc : 0 ≤ c) (Y : Ω → ℝ) (hYm : Measurable Y)
    {M : ℝ} (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ M) :
    Integrable (fun ω => Real.exp (c * Y ω)) P := by
  refine Integrable.of_bound (Measurable.exp (measurable_const.mul hYm)).aestronglyMeasurable
    (Real.exp (c * M)) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hY ω).2 hc)

lemma effSize_nonneg_and_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℕ} (hm : 2 ≤ m) (Y : Ω → ℝ) (hYm : Measurable Y)
    {a : ℝ} (_ha0 : 0 ≤ a) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ a) :
    0 ≤ effSize P m Y ∧ effSize P m Y ≤ a := by
  have hm_ne : m ≠ 1 := by omega
  have hm_gt1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlogm_pos : 0 < Real.log m := Real.log_pos hm_gt1
  unfold effSize
  rw [if_neg hm_ne]
  have hint := integrable_exp_mul P (Real.log m) hlogm_pos.le Y hYm hY
  have h1 : (1 : ℝ) ≤ ∫ ω, Real.exp (Real.log m * Y ω) ∂P := by
    calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂P := by simp
      _ ≤ ∫ ω, Real.exp (Real.log m * Y ω) ∂P :=
        integral_mono (integrable_const _) hint (fun ω => by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hlogm_pos.le (hY ω).1))
  have h2 : ∫ ω, Real.exp (Real.log m * Y ω) ∂P ≤ Real.exp (Real.log m * a) := by
    calc ∫ ω, Real.exp (Real.log m * Y ω) ∂P
        ≤ ∫ _ω, Real.exp (Real.log m * a) ∂P :=
          integral_mono hint (integrable_const _) (fun ω =>
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hY ω).2 hlogm_pos.le))
      _ = Real.exp (Real.log m * a) := by simp
  constructor
  · exact div_nonneg (Real.log_nonneg h1) hlogm_pos.le
  · rw [div_le_iff₀ hlogm_pos]
    calc Real.log (∫ ω, Real.exp (Real.log m * Y ω) ∂P)
        ≤ Real.log (Real.exp (Real.log m * a)) :=
          Real.log_le_log (by linarith) h2
      _ = Real.log m * a := Real.log_exp _
      _ = a * Real.log m := mul_comm _ _

lemma integral_exp_sum_eq_prod {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (Y : Fin n → Ω → ℝ)
    (hYm : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P)
    (hY : ∀ j ω, 0 ≤ Y j ω ∧ Y j ω ≤ 1) (s : Finset (Fin n)) :
    ∫ ω, Real.exp (c * ∑ j ∈ s, Y j ω) ∂P = ∏ j ∈ s, ∫ ω, Real.exp (c * Y j ω) ∂P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih]
    have hsum : (fun ω => Real.exp (c * ∑ j ∈ insert a s, Y j ω)) =
        (fun ω => Real.exp (c * Y a ω) * Real.exp (c * ∑ j ∈ s, Y j ω)) := by
      ext ω
      rw [Finset.sum_insert ha, mul_add, Real.exp_add]
    rw [hsum]
    let A0 : Finset (Fin n) := {a}
    have hdisj : Disjoint A0 s := Finset.disjoint_singleton_left.mpr ha
    have hI := hind.indepFun_finset A0 s hdisj hYm
    let φ : (A0 → ℝ) → ℝ := fun v => Real.exp (c * v ⟨a, Finset.mem_singleton_self a⟩)
    let ψ : (s → ℝ) → ℝ := fun v => Real.exp (c * ∑ j : s, v j)
    have hφ : Measurable φ :=
      Measurable.exp (measurable_const.mul (measurable_pi_apply _))
    have hψ : Measurable ψ :=
      Measurable.exp (measurable_const.mul (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)))
    have hInd := hI.comp hφ hψ
    have hmeas1 : Measurable (fun ω => Real.exp (c * Y a ω)) :=
      Measurable.exp (measurable_const.mul (hYm a))
    have hmeas2 : Measurable (fun ω => Real.exp (c * ∑ j ∈ s, Y j ω)) :=
      Measurable.exp (measurable_const.mul (Finset.measurable_sum _ (fun j _ => hYm j)))
    have hEq1 : (φ ∘ fun ω (i : A0) => Y i ω) =
        fun ω => Real.exp (c * Y a ω) := rfl
    have hEq2 : (ψ ∘ fun ω (i : s) => Y i ω) =
        fun ω => Real.exp (c * ∑ j ∈ s, Y j ω) := by
      ext ω
      simp only [ψ, Function.comp_apply]
      rw [Finset.sum_coe_sort s (fun j => Y j ω)]
    rw [hEq1, hEq2] at hInd
    exact hInd.integral_fun_mul_eq_mul_integral hmeas1.aestronglyMeasurable
      hmeas2.aestronglyMeasurable

lemma effSize_le_trunc_add_prob {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℕ} (hm : 2 ≤ m) (X : Ω → ℝ) (hXm : Measurable X)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) :
    effSize P m X ≤
      effSize P m (fun ω => if X ω < 1/4 then X ω else 0) +
        ((m : ℝ) - 1) / Real.log m * (P {ω | 1/4 ≤ X ω}).toReal := by
  have hm_ne : m ≠ 1 := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm_gt1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlogm_pos : 0 < Real.log m := Real.log_pos hm_gt1
  let X' : Ω → ℝ := fun ω => if X ω < 1/4 then X ω else 0
  have hX'm : Measurable X' := hXm.ite (measurableSet_lt hXm measurable_const) measurable_const
  have hX' : ∀ ω, 0 ≤ X' ω ∧ X' ω ≤ 1 := fun ω => by
    dsimp [X']; split_ifs
    · exact hX ω
    · exact ⟨le_rfl, zero_le_one⟩
  have hpt : ∀ ω, Real.exp (Real.log m * X ω) ≤
      Real.exp (Real.log m * X' ω) + ((m : ℝ) - 1) * ({ω | 1/4 ≤ X ω}).indicator (fun _ => 1) ω := by
    intro ω
    dsimp [X']
    by_cases h : X ω < 1/4
    · have hnot : ω ∉ ({ω | 1/4 ≤ X ω} : Set Ω) := fun hmem => (not_le.mpr h) hmem
      rw [if_pos h, Set.indicator_of_notMem hnot, mul_zero, add_zero]
    · have hmem : ω ∈ ({ω | 1/4 ≤ X ω} : Set Ω) := not_lt.mp h
      rw [if_neg h, mul_zero, Real.exp_zero, Set.indicator_of_mem hmem, mul_one]
      have hle : Real.exp (Real.log m * X ω) ≤ m := by
        calc Real.exp (Real.log m * X ω)
            ≤ Real.exp (Real.log m * 1) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hX ω).2 hlogm_pos.le)
          _ = m := by rw [mul_one, Real.exp_log hm_pos]
      linarith
  have hintX := integrable_exp_mul P (Real.log m) hlogm_pos.le X hXm hX
  have hintX' := integrable_exp_mul P (Real.log m) hlogm_pos.le X' hX'm hX'
  have hSmeas : MeasurableSet {ω | 1/4 ≤ X ω} := measurableSet_le measurable_const hXm
  have hintInd : Integrable (fun ω => ((m : ℝ) - 1) * ({ω | 1/4 ≤ X ω}).indicator (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hSmeas).const_mul _
  have hmono := integral_mono hintX (hintX'.add hintInd) hpt
  simp only [Pi.add_apply] at hmono
  have hind1 : ∫ a, ({ω | 1/4 ≤ X ω}).indicator (fun _ => (1 : ℝ)) a ∂P =
      (P {ω | 1/4 ≤ X ω}).toReal := by
    rw [integral_indicator_const (1 : ℝ) hSmeas, smul_eq_mul, mul_one, measureReal_def]
  rw [integral_add hintX' hintInd, integral_const_mul, hind1] at hmono
  set E' := ∫ ω, Real.exp (Real.log m * X' ω) ∂P
  set p := (P {ω | 1/4 ≤ X ω}).toReal
  have hE'1 : 1 ≤ E' := by
    calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂P := by simp
      _ ≤ E' := integral_mono (integrable_const _) hintX' (fun ω => by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hlogm_pos.le (hX' ω).1))
  have hm1_nn : 0 ≤ (m : ℝ) - 1 := by linarith
  have hp_nn : 0 ≤ p := ENNReal.toReal_nonneg
  have hE_le : ∫ ω, Real.exp (Real.log m * X ω) ∂P ≤ E' * Real.exp (((m : ℝ) - 1) * p) := by
    calc ∫ ω, Real.exp (Real.log m * X ω) ∂P
        ≤ E' + ((m : ℝ) - 1) * p := hmono
      _ ≤ E' * (1 + ((m : ℝ) - 1) * p) := by
          have h := mul_le_mul_of_nonneg_right hE'1 (mul_nonneg hm1_nn hp_nn)
          nlinarith [h]
      _ ≤ E' * Real.exp (((m : ℝ) - 1) * p) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith [Real.add_one_le_exp (((m : ℝ) - 1) * p)]
  have hE_pos : 0 < ∫ ω, Real.exp (Real.log m * X ω) ∂P := by
    calc (0 : ℝ) < 1 := one_pos
      _ ≤ ∫ ω, Real.exp (Real.log m * X ω) ∂P := by
        calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂P := by simp
          _ ≤ _ := integral_mono (integrable_const _) hintX (fun ω => by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (mul_nonneg hlogm_pos.le (hX ω).1))
  have hlog_le : Real.log (∫ ω, Real.exp (Real.log m * X ω) ∂P) ≤
      Real.log E' + ((m : ℝ) - 1) * p := by
    calc Real.log (∫ ω, Real.exp (Real.log m * X ω) ∂P)
        ≤ Real.log (E' * Real.exp (((m : ℝ) - 1) * p)) := Real.log_le_log hE_pos hE_le
      _ = Real.log E' + ((m : ℝ) - 1) * p := by
          rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
  unfold effSize
  rw [if_neg hm_ne, if_neg hm_ne]
  have hfin : Real.log (∫ ω, Real.exp (Real.log m * X ω) ∂P) / Real.log m ≤
      (Real.log E' + ((m : ℝ) - 1) * p) / Real.log m :=
    div_le_div_of_nonneg_right hlog_le hlogm_pos.le
  calc Real.log (∫ ω, Real.exp (Real.log m * X ω) ∂P) / Real.log m
      ≤ (Real.log E' + ((m : ℝ) - 1) * p) / Real.log m := hfin
    _ = Real.log E' / Real.log m + ((m : ℝ) - 1) / Real.log m * p := by ring

lemma small_step_tail_pow {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} (Y : Fin k → Ω → ℝ) (hYm : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) (hY : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω < 1/4) (r : ℕ) :
    P {ω | (r : ℝ) / 2 ≤ ∑ i, Y i ω} ≤ (P {ω | 1/4 ≤ ∑ i, Y i ω}) ^ r := by
  let S_part : ℕ → Ω → ℝ := fun t ω => ∑ i : Fin k, if i.1 < t then Y i ω else 0
  have hS_zero : ∀ ω, S_part 0 ω = 0 := fun ω => by simp [S_part]
  have hS_full : ∀ ω, S_part k ω = ∑ i : Fin k, Y i ω := fun ω => by
    simp only [S_part]; apply Finset.sum_congr rfl; intro i _; simp [i.isLt]
  have hS_succ : ∀ (t : Fin k) ω, S_part (t.1 + 1) ω = S_part t.1 ω + Y t ω := by
    intro t ω
    dsimp [S_part]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ t),
        ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ t)]
    simp only [Nat.lt_succ_self, if_true, Nat.lt_irrefl, if_false, zero_add]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ t := Finset.ne_of_mem_erase hi
    have hiff : i.1 < t.1 + 1 ↔ i.1 < t.1 := by
      have : i.1 ≠ t.1 := fun h => hne (Fin.ext h)
      omega
    simp [hiff]
  have hS_mono : ∀ {a b : ℕ} (hab : a ≤ b) ω, S_part a ω ≤ S_part b ω := by
    intro a b hab ω
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact (hY i ω).1
    · exact le_rfl
  have hS_meas : ∀ t, Measurable (S_part t) := fun t =>
    Finset.measurable_sum _ (fun i _ => by
      by_cases h : i.1 < t <;> simp [h, hYm i, measurable_const])
  simp_rw [← hS_full]
  induction r with
  | zero => simp [prob_le_one]
  | succ r ih =>
    rcases eq_or_ne r 0 with rfl | hr0
    · simp only [Nat.cast_zero, zero_add, pow_one]
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      linarith
    · let E : Fin k → Set Ω := fun t => {ω | S_part t.1 ω < 1/4 ∧ 1/4 ≤ S_part (t.1 + 1) ω}
      have hE_meas : ∀ t, MeasurableSet (E t) := fun t =>
        (measurableSet_lt (hS_meas t.1) measurable_const).inter
          (measurableSet_le measurable_const (hS_meas (t.1 + 1)))
      have hE_disj : Pairwise (fun t₁ t₂ => Disjoint (E t₁) (E t₂)) := by
        intro t₁ t₂ hne
        rw [Set.disjoint_left]
        intro ω h1 h2
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
        · have hle : S_part (t₁.1 + 1) ω ≤ S_part t₂.1 ω := hS_mono (by omega) ω
          linarith [h1.2, h2.1]
        · have hle : S_part (t₂.1 + 1) ω ≤ S_part t₁.1 ω := hS_mono (by omega) ω
          linarith [h2.2, h1.1]
      have hE_union : (⋃ t : Fin k, E t) = {ω | 1/4 ≤ S_part k ω} := by
        ext ω
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, E]
        constructor
        · rintro ⟨t, _, ht2⟩
          exact ht2.trans (hS_mono t.isLt ω)
        · intro hω
          classical
          have hex : ∃ t : ℕ, 1/4 ≤ S_part t ω := ⟨k, hω⟩
          let t₀ := Nat.find hex
          have ht₀_spec : 1/4 ≤ S_part t₀ ω := Nat.find_spec hex
          have ht₀_ne : t₀ ≠ 0 := by
            intro h0
            rw [h0, hS_zero] at ht₀_spec
            linarith
          have ht₀_le : t₀ ≤ k := Nat.find_le hω
          obtain ⟨t, ht_eq⟩ := Nat.exists_eq_succ_of_ne_zero ht₀_ne
          have ht_lt : t < k := by omega
          have ht_prev : S_part t ω < 1/4 :=
            lt_of_not_ge (Nat.find_min hex (by omega : t < t₀))
          refine ⟨⟨t, ht_lt⟩, ht_prev, ?_⟩
          have hidx : (⟨t, ht_lt⟩ : Fin k).1 + 1 = t₀ := by simp [ht_eq]
          rw [hidx]; exact ht₀_spec
      let tail : Fin k → Ω → ℝ := fun t ω =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => t.1 < i.1), Y i ω
      have htail_le : ∀ t ω, tail t ω ≤ S_part k ω := fun t ω => by
        rw [hS_full]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => (hY i ω).1)
      have hsub : {ω | ((r + 1 : ℕ) : ℝ) / 2 ≤ S_part k ω} ⊆
          ⋃ t : Fin k, (E t ∩ {ω | (r : ℝ) / 2 ≤ tail t ω}) := by
        intro ω hω
        have h14 : ω ∈ {ω | 1/4 ≤ S_part k ω} := by
          simp only [Set.mem_setOf_eq] at hω ⊢
          have hr1 : (1 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ r + 1)
          linarith
        rw [← hE_union, Set.mem_iUnion] at h14
        obtain ⟨t, ht⟩ := h14
        rw [Set.mem_iUnion]
        refine ⟨t, ht, ?_⟩
        simp only [Set.mem_setOf_eq] at hω ⊢
        have hsum_eq : S_part k ω = S_part (t.1 + 1) ω + tail t ω := by
          rw [hS_full]
          dsimp [S_part, tail]
          have : ∑ i : Fin k, Y i ω =
              ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.1 < t.1 + 1), Y i ω +
              ∑ i ∈ Finset.univ.filter (fun i : Fin k => ¬(i.1 < t.1 + 1)), Y i ω :=
            (Finset.sum_filter_add_sum_filter_not _ _ _).symm
          rw [this]
          congr 1
          · rw [← Finset.sum_filter]
          · apply Finset.sum_congr
            · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]; omega
            · intros; rfl
        have hlt_half : S_part (t.1 + 1) ω < 1/2 := by
          rw [hS_succ]
          linarith [ht.1, (hY t ω).2]
        push_cast at hω
        linarith
      have h_indep : ∀ t : Fin k,
          P (E t ∩ {ω | (r : ℝ) / 2 ≤ tail t ω}) = P (E t) * P {ω | (r : ℝ) / 2 ≤ tail t ω} := by
        intro t
        let A : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => i.1 ≤ t.1)
        let B : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => t.1 < i.1)
        have hAB : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro i hiA hiB
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
          omega
        have hI := hind.indepFun_finset A B hAB hYm
        apply hI.meas_inter
        · let sA : Set (A → ℝ) :=
            {v | (∑ i : A, if i.1.1 < t.1 then v i else 0) < 1 / 4} ∩
            {v | 1 / 4 ≤ (∑ i : A, if i.1.1 < t.1 + 1 then v i else 0)}
          refine ⟨sA, ?_, ?_⟩
          · refine MeasurableSet.inter ?_ ?_
            · refine measurableSet_lt (Finset.measurable_sum _ fun i _ => ?_) measurable_const
              by_cases h : i.1.1 < t.1 <;> simp [h, measurable_pi_apply, measurable_const]
            · refine measurableSet_le measurable_const (Finset.measurable_sum _ fun i _ => ?_)
              by_cases h : i.1.1 < t.1 + 1 <;> simp [h, measurable_pi_apply, measurable_const]
          · ext ω
            simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, sA, E, S_part]
            have eq1 : (∑ i : A, if i.1.1 < t.1 then Y i.1 ω else 0) =
                ∑ i : Fin k, if i.1 < t.1 then Y i ω else 0 := by
              rw [Finset.sum_coe_sort A (fun i => if i.1 < t.1 then Y i ω else 0)]
              rw [← Finset.sum_subset (Finset.subset_univ A)]
              intro i _ hiA
              simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hiA
              simp [show ¬(i.1 < t.1) by omega]
            have eq2 : (∑ i : A, if i.1.1 < t.1 + 1 then Y i.1 ω else 0) =
                ∑ i : Fin k, if i.1 < t.1 + 1 then Y i ω else 0 := by
              rw [Finset.sum_coe_sort A (fun i => if i.1 < t.1 + 1 then Y i ω else 0)]
              rw [← Finset.sum_subset (Finset.subset_univ A)]
              intro i _ hiA
              simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hiA
              simp [show ¬(i.1 < t.1 + 1) by omega]
            rw [eq1, eq2]
        · refine ⟨{v | (r : ℝ) / 2 ≤ ∑ i : B, v i}, ?_, ?_⟩
          · exact measurableSet_le measurable_const
              (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
          · ext ω
            simp only [Set.mem_preimage, Set.mem_setOf_eq, tail]
            rw [Finset.sum_coe_sort B (fun i => Y i ω)]
      calc P {ω | ((r + 1 : ℕ) : ℝ) / 2 ≤ S_part k ω}
          ≤ P (⋃ t : Fin k, (E t ∩ {ω | (r : ℝ) / 2 ≤ tail t ω})) := measure_mono hsub
        _ ≤ ∑ t : Fin k, P (E t ∩ {ω | (r : ℝ) / 2 ≤ tail t ω}) :=
            measure_iUnion_fintype_le _ _
        _ = ∑ t : Fin k, P (E t) * P {ω | (r : ℝ) / 2 ≤ tail t ω} := by
            simp_rw [h_indep]
        _ ≤ ∑ t : Fin k, P (E t) * P {ω | (r : ℝ) / 2 ≤ S_part k ω} := by
            refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ zero_le
            exact measure_mono (fun ω hω => le_trans hω (htail_le t ω))
        _ = (∑ t : Fin k, P (E t)) * P {ω | (r : ℝ) / 2 ≤ S_part k ω} :=
            (Finset.sum_mul _ _ _).symm
        _ = P (⋃ t : Fin k, E t) * P {ω | (r : ℝ) / 2 ≤ S_part k ω} := by
            rw [measure_iUnion (fun i j hij => hE_disj hij) hE_meas, tsum_fintype]
        _ = P {ω | 1/4 ≤ S_part k ω} * P {ω | (r : ℝ) / 2 ≤ S_part k ω} := by
            rw [hE_union]
        _ ≤ P {ω | 1/4 ≤ S_part k ω} * (P {ω | 1/4 ≤ S_part k ω}) ^ r :=
            mul_le_mul_of_nonneg_left ih zero_le
        _ = (P {ω | 1/4 ≤ S_part k ω}) ^ (r + 1) := by ring

lemma small_step_block_prob {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n : ℕ} (hm : 2 ≤ m) (Y : Fin n → Ω → ℝ)
    (hYm : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P)
    (hY : ∀ j ω, 0 ≤ Y j ω ∧ Y j ω < 1/4) (b : Finset (Fin n))
    (hb : 2 ≤ ∑ j ∈ b, effSize P m (Y j)) :
    1 / (2 * (m : ℝ)) < (P {ω | 1/4 ≤ ∑ j ∈ b, Y j ω}).toReal := by
  let k := b.card
  let e : Fin k ↪ Fin n :=
    ⟨fun i => (b.equivFin.symm i).1, fun i₁ i₂ h => by
      apply b.equivFin.symm.injective
      exact Subtype.ext h⟩
  let Z : Fin k → Ω → ℝ := fun i ω => Y (e i) ω
  have hZm : ∀ i, Measurable (Z i) := fun i => hYm (e i)
  have hZind : iIndepFun Z P := hind.precomp e.injective
  have hZ : ∀ i ω, 0 ≤ Z i ω ∧ Z i ω < 1/4 := fun i ω => hY (e i) ω
  have hsum_eq : ∀ ω, ∑ i : Fin k, Z i ω = ∑ j ∈ b, Y j ω := fun ω => by
    rw [← Finset.sum_coe_sort b (fun j => Y j ω)]
    exact Fintype.sum_equiv b.equivFin.symm (fun i : Fin k => Z i ω) (fun j : b => Y j ω)
      (fun i => rfl)
  have hm_ne : m ≠ 1 := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm_gt1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlogm_pos : 0 < Real.log m := Real.log_pos hm_gt1
  have hY01 : ∀ j ω, 0 ≤ Y j ω ∧ Y j ω ≤ 1 := fun j ω => ⟨(hY j ω).1, by linarith [(hY j ω).2]⟩
  have hE_ge : (m : ℝ) ^ (2 : ℝ) ≤ ∫ ω, Real.exp (Real.log m * ∑ j ∈ b, Y j ω) ∂P := by
    have hprod := integral_exp_sum_eq_prod P (Real.log m) hlogm_pos.le Y hYm hind hY01 b
    have hlog_eq : ∑ j ∈ b, effSize P m (Y j) =
        Real.log (∏ j ∈ b, ∫ ω, Real.exp (Real.log m * Y j ω) ∂P) / Real.log m := by
      have hpos : ∀ j ∈ b, ∫ ω, Real.exp (Real.log m * Y j ω) ∂P ≠ 0 := fun j _ => by
        have hint := integrable_exp_mul P (Real.log m) hlogm_pos.le (Y j) (hYm j) (hY01 j)
        have h1 : (1 : ℝ) ≤ ∫ ω, Real.exp (Real.log m * Y j ω) ∂P := by
          calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂P := by simp
            _ ≤ _ := integral_mono (integrable_const (1 : ℝ)) hint (fun ω => by
              rw [← Real.exp_zero]
              exact Real.exp_le_exp.mpr (mul_nonneg hlogm_pos.le (hY j ω).1))
        linarith
      rw [Real.log_prod hpos, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _; unfold effSize; rw [if_neg hm_ne]
    rw [hprod]
    have hlog_prod : Real.log m * 2 ≤ Real.log (∏ j ∈ b, ∫ ω, Real.exp (Real.log m * Y j ω) ∂P) := by
      rw [mul_comm, ← le_div_iff₀ hlogm_pos]
      calc (2 : ℝ) ≤ ∑ j ∈ b, effSize P m (Y j) := hb
        _ = Real.log (∏ j ∈ b, ∫ ω, Real.exp (Real.log m * Y j ω) ∂P) / Real.log m := hlog_eq
    have hprod_pos : 0 < ∏ j ∈ b, ∫ ω, Real.exp (Real.log m * Y j ω) ∂P := by
      apply Finset.prod_pos
      intro j _
      have hint := integrable_exp_mul P (Real.log m) hlogm_pos.le (Y j) (hYm j) (hY01 j)
      calc (0 : ℝ) < 1 := one_pos
        _ = ∫ _ω, (1 : ℝ) ∂P := by simp
        _ ≤ _ := integral_mono (integrable_const (1 : ℝ)) hint (fun ω => by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hlogm_pos.le (hY j ω).1))
    calc (m : ℝ) ^ (2 : ℝ) = Real.exp (Real.log m * 2) := by
          rw [Real.rpow_def_of_pos hm_pos]
      _ ≤ Real.exp (Real.log (∏ j ∈ b, ∫ ω, Real.exp (Real.log m * Y j ω) ∂P)) :=
          Real.exp_le_exp.mpr hlog_prod
      _ = ∏ j ∈ b, ∫ ω, Real.exp (Real.log m * Y j ω) ∂P := Real.exp_log hprod_pos
  set p := (P {ω | 1/4 ≤ ∑ j ∈ b, Y j ω}).toReal
  have hp_gt : 1 / (2 * Real.sqrt m) < p := by
    by_contra hle
    push_neg at hle
    have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
    have hp_prod : Real.sqrt m * p ≤ 1 / 2 := by
      calc Real.sqrt m * p ≤ Real.sqrt m * (1 / (2 * Real.sqrt m)) :=
            mul_le_mul_of_nonneg_left hle hsqrt_pos.le
        _ = 1 / 2 := by field_simp [hsqrt_pos.ne']
    have hpt : ∀ ω, Real.exp (Real.log m * ∑ i : Fin k, Z i ω) ≤
        Real.sqrt m + ∑ r ∈ Finset.Icc 1 k,
          (Real.sqrt m) ^ (r + 1) *
            ({ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      set Sω := ∑ i : Fin k, Z i ω
      have hS_nn : 0 ≤ Sω := Finset.sum_nonneg (fun i _ => (hZ i ω).1)
      have hS_ub : Sω < ((k : ℝ) + 1) / 2 := by
        have hk_ub : Sω ≤ (k : ℝ) * (1 / 4) := by
          calc Sω ≤ ∑ _i : Fin k, (1 / 4 : ℝ) := Finset.sum_le_sum (fun i _ => (hZ i ω).2.le)
            _ = (k : ℝ) * (1 / 4) := by simp
        linarith
      have hsqrt_exp : ∀ (r : ℕ), (Real.sqrt m) ^ r = Real.exp (Real.log m * ((r : ℝ) / 2)) := by
        intro r
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hm_pos.le,
          Real.rpow_def_of_pos hm_pos]
        congr 1; ring
      let r₀ := ⌊2 * Sω⌋₊
      have hr₀_le : (r₀ : ℝ) ≤ 2 * Sω := Nat.floor_le (by linarith)
      have hr₀_lt : 2 * Sω < (r₀ : ℝ) + 1 := Nat.lt_floor_add_one _
      rcases eq_or_ne r₀ 0 with hr0 | hrpos
      · have hS_half : Sω ≤ 1 / 2 := by rw [hr0] at hr₀_lt; push_cast at hr₀_lt; linarith
        have h1 : Real.exp (Real.log m * Sω) ≤ Real.sqrt m := by
          calc Real.exp (Real.log m * Sω)
              ≤ Real.exp (Real.log m * (1 / 2)) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS_half hlogm_pos.le)
            _ = Real.sqrt m := by
                have := hsqrt_exp 1; simp only [pow_one, Nat.cast_one] at this; exact this.symm
        have hsum_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 k, (Real.sqrt m) ^ (r + 1) *
            ({ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).indicator (fun _ => (1 : ℝ)) ω :=
          Finset.sum_nonneg (fun r _ => mul_nonneg (pow_nonneg hsqrt_pos.le _)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        change Real.exp (Real.log m * Sω) ≤ _
        linarith
      · have hr₀_ge1 : 1 ≤ r₀ := Nat.one_le_iff_ne_zero.mpr hrpos
        have hr₀_lek : r₀ ≤ k := by
          have : (r₀ : ℝ) < (k : ℝ) + 1 := by linarith
          exact_mod_cast (by
            have h1 : (r₀ : ℝ) < (k + 1 : ℕ) := by push_cast; exact this
            exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp h1))
        have hr₀_mem : r₀ ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hr₀_ge1, hr₀_lek⟩
        have hterm : Real.exp (Real.log m * Sω) ≤ (Real.sqrt m) ^ (r₀ + 1) *
            ({ω | (r₀ : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).indicator (fun _ => (1 : ℝ)) ω := by
          rw [Set.indicator_of_mem (by show (r₀ : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω; change (r₀ : ℝ) / 2 ≤ Sω; linarith),
            mul_one, hsqrt_exp]
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ hlogm_pos.le
          have h1 : (r₀ : ℝ) + 1 = ((r₀ + 1 : ℕ) : ℝ) := by push_cast; rfl
          rw [← h1]
          linarith
        have hsum_ge := Finset.single_le_sum (f := fun r : ℕ => (Real.sqrt m) ^ (r + 1) *
            ({ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).indicator (fun _ => (1 : ℝ)) ω)
          (fun r _ => mul_nonneg (pow_nonneg hsqrt_pos.le _)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) hr₀_mem
        linarith [hsqrt_pos]
    have hZ_meas_sum : Measurable (fun ω => ∑ i : Fin k, Z i ω) :=
      Finset.measurable_sum _ (fun i _ => hZm i)
    have hint_lhs : Integrable (fun ω => Real.exp (Real.log m * ∑ i : Fin k, Z i ω)) P := by
      have hub : ∀ ω, 0 ≤ ∑ i : Fin k, Z i ω ∧ ∑ i : Fin k, Z i ω ≤ (k : ℝ) := fun ω =>
        ⟨Finset.sum_nonneg (fun i _ => (hZ i ω).1),
         (Finset.sum_le_sum (fun i _ => (by linarith [(hZ i ω).2] : Z i ω ≤ 1))).trans (by simp)⟩
      exact integrable_exp_mul P (Real.log m) hlogm_pos.le _ hZ_meas_sum hub
    have hint_term : ∀ r ∈ Finset.Icc 1 k, Integrable (fun ω => (Real.sqrt m) ^ (r + 1) *
        ({ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).indicator (fun _ => (1 : ℝ)) ω) P := fun r _ =>
      ((integrable_const (1 : ℝ)).indicator (measurableSet_le measurable_const hZ_meas_sum)).const_mul _
    have hmono := integral_mono hint_lhs ((integrable_const (Real.sqrt m)).add (integrable_finsetSum _ hint_term)) hpt
    simp only [Pi.add_apply] at hmono
    rw [integral_add (integrable_const _) (integrable_finsetSum _ hint_term),
      integral_const, smul_eq_mul, probReal_univ, one_mul,
      integral_finset_sum _ hint_term] at hmono
    have hterm_eq : ∀ r ∈ Finset.Icc 1 k,
        ∫ ω, (Real.sqrt m) ^ (r + 1) *
          ({ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).indicator (fun _ => (1 : ℝ)) ω ∂P ≤
        Real.sqrt m * (Real.sqrt m * p) ^ r := by
      intro r _
      rw [integral_const_mul,
        integral_indicator_const (1 : ℝ) (measurableSet_le measurable_const hZ_meas_sum),
        smul_eq_mul, mul_one, measureReal_def]
      have hpow := small_step_tail_pow P Z hZm hZind hZ r
      have hpow_real : (P {ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).toReal ≤ p ^ r := by
        have hpeq : p = (P {ω | 1/4 ≤ ∑ i : Fin k, Z i ω}).toReal := by
          dsimp [p]; congr 2; ext ω; simp [hsum_eq ω]
        rw [hpeq]
        calc (P {ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).toReal
            ≤ ((P {ω | 1/4 ≤ ∑ i : Fin k, Z i ω}) ^ r).toReal :=
              ENNReal.toReal_mono (ENNReal.pow_ne_top (measure_ne_top P _)) hpow
          _ = (P {ω | 1/4 ≤ ∑ i : Fin k, Z i ω}).toReal ^ r := ENNReal.toReal_pow _ r
      calc (Real.sqrt m) ^ (r + 1) * (P {ω | (r : ℝ) / 2 ≤ ∑ i : Fin k, Z i ω}).toReal
          ≤ (Real.sqrt m) ^ (r + 1) * p ^ r :=
            mul_le_mul_of_nonneg_left hpow_real (pow_nonneg hsqrt_pos.le _)
        _ = Real.sqrt m * (Real.sqrt m * p) ^ r := by rw [pow_succ', mul_pow]; ring
    have hsum_bound : ∑ r ∈ Finset.Icc 1 k, (Real.sqrt m * p) ^ r ≤ 1 := by
      calc ∑ r ∈ Finset.Icc 1 k, (Real.sqrt m * p) ^ r
          ≤ ∑ r ∈ Finset.Icc 1 k, (1 / 2 : ℝ) ^ r :=
            Finset.sum_le_sum (fun r _ => pow_le_pow_left₀
              (mul_nonneg hsqrt_pos.le ENNReal.toReal_nonneg) hp_prod r)
        _ ≤ ∑ r ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ r - 1 := by
            have h0 : (Finset.Icc 1 k : Finset ℕ) = (Finset.range (k + 1)).erase 0 := by
              ext r; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
            rw [h0, Finset.sum_erase_eq_sub (Finset.mem_range.mpr (Nat.succ_pos k))]
            simp
        _ ≤ 1 := by
            have hgeom : ∑ r ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ r =
                2 * (1 - (1 / 2 : ℝ) ^ (k + 1)) := by
              rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
              ring
            rw [hgeom]
            have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) := by positivity
            linarith
    have hE_lt : ∫ ω, Real.exp (Real.log m * ∑ j ∈ b, Y j ω) ∂P < (m : ℝ) ^ (2 : ℝ) := by
      have heq_int : ∫ ω, Real.exp (Real.log m * ∑ j ∈ b, Y j ω) ∂P =
          ∫ ω, Real.exp (Real.log m * ∑ i : Fin k, Z i ω) ∂P := by
        congr 1; ext ω; rw [hsum_eq ω]
      rw [heq_int]
      have h2sqrt : 2 * Real.sqrt m < (m : ℝ) ^ (2 : ℝ) := by
        have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
        have hsq : (2 * Real.sqrt m) ^ 2 < ((m : ℝ) ^ (2 : ℝ)) ^ 2 := by
          have h2 : (m : ℝ) ^ (2 : ℝ) = (m : ℝ) ^ (2 : ℕ) := Real.rpow_natCast _ 2
          rw [mul_pow, Real.sq_sqrt hm_pos.le, h2]
          have h4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
          nlinarith [mul_nonneg (sub_nonneg.mpr h4) (sq_nonneg (m : ℝ)),
            mul_nonneg (sub_nonneg.mpr hm2) hm_pos.le]
        by_contra hcon
        have hcon' : (m : ℝ) ^ (2 : ℝ) ≤ 2 * Real.sqrt m := not_lt.mp hcon
        have hpw := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ (2 : ℝ)) hcon' 2
        linarith
      calc ∫ ω, Real.exp (Real.log m * ∑ i : Fin k, Z i ω) ∂P
          ≤ Real.sqrt m + ∑ r ∈ Finset.Icc 1 k, Real.sqrt m * (Real.sqrt m * p) ^ r :=
            hmono.trans (add_le_add_right (Finset.sum_le_sum hterm_eq) _)
        _ = Real.sqrt m * (1 + ∑ r ∈ Finset.Icc 1 k, (Real.sqrt m * p) ^ r) := by
            rw [← Finset.mul_sum]; ring
        _ ≤ Real.sqrt m * (1 + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hsqrt_pos.le
        _ = 2 * Real.sqrt m := by ring
        _ < (m : ℝ) ^ (2 : ℝ) := h2sqrt
    linarith
  have hm_ge1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hsqrt_le : Real.sqrt m ≤ m := by
    calc Real.sqrt m ≤ Real.sqrt (m * m) := Real.sqrt_le_sqrt (by nlinarith)
      _ = m := Real.sqrt_mul_self hm_pos.le
  calc 1 / (2 * (m : ℝ)) ≤ 1 / (2 * Real.sqrt m) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ < p := hp_gt

theorem lemma_4_group_tail_proved :
    ∃ θ c : ℝ, 0 < θ ∧ 0 < c ∧
      ∀ (m n : ℕ), 2 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin n → Ω → ℝ),
        (∀ j, Measurable (X j)) → iIndepFun X P →
        (∀ j ω, 0 ≤ X j ω ∧ X j ω ≤ 1) →
        ∀ s : Finset (Fin n),
          (P {ω | ∑ j ∈ s, X j ω < θ}).toReal ≤
            Real.exp (-(c * (∑ j ∈ s, effSize P m (X j) - 16) / m)) := by
  refine ⟨1 / 4, 1 / 12, by norm_num, by norm_num, ?_⟩
  intro m n hm Ω _ P _ X hmeas hind hX s
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set B := ∑ j ∈ s, effSize P m (X j)
  by_cases hB : B ≤ 16
  · have harg : 0 ≤ -(1 / 12 * (B - 16) / (m : ℝ)) := by
      apply neg_nonneg.mpr
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hm_pos.le
    calc (P {ω | ∑ j ∈ s, X j ω < 1 / 4}).toReal ≤ 1 :=
        ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P))
      _ ≤ Real.exp (-(1 / 12 * (B - 16) / (m : ℝ))) := Real.one_le_exp harg
  · push_neg at hB
    let p : Fin n → ℝ := fun j => (P {ω | 1 / 4 ≤ X j ω}).toReal
    by_cases hp_sum : 1 / 12 * (B - 16) / (m : ℝ) ≤ ∑ j ∈ s, p j
    · have hsub : {ω | ∑ j ∈ s, X j ω < 1 / 4} ⊆ ⋂ j ∈ s, {ω | X j ω < 1 / 4} := by
        intro ω hω
        simp only [Set.mem_iInter, Set.mem_setOf_eq] at hω ⊢
        intro j hj
        by_contra hge
        push_neg at hge
        have hle : X j ω ≤ ∑ j' ∈ s, X j' ω :=
          Finset.single_le_sum (fun j' _ => (hX j' ω).1) hj
        linarith
      have hmeas_lt : ∀ j ∈ s, MeasurableSet[MeasurableSpace.comap (X j) inferInstance]
          {ω | X j ω < 1 / 4} := fun j _ =>
        ⟨{x : ℝ | x < 1 / 4}, measurableSet_Iio, rfl⟩
      have hind_meas := hind.meas_biInter hmeas_lt
      have hprod : (P (⋂ j ∈ s, {ω | X j ω < 1 / 4})).toReal =
          ∏ j ∈ s, (P {ω | X j ω < 1 / 4}).toReal := by
        rw [hind_meas, ENNReal.toReal_prod]
      have hcompl : ∀ j, (P {ω | X j ω < 1 / 4}).toReal = 1 - p j := fun j => by
        have hmset : MeasurableSet {ω | X j ω < 1 / 4} := measurableSet_lt (hmeas j) measurable_const
        have hceq : {ω | X j ω < 1 / 4}ᶜ = {ω | 1 / 4 ≤ X j ω} := by
          ext ω; simp [not_lt]
        have hsum := measure_add_measure_compl hmset (μ := P)
        have hsum_real := congrArg ENNReal.toReal hsum
        rw [measure_univ, ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _),
          ENNReal.toReal_one, hceq] at hsum_real
        dsimp [p]
        linarith
      calc (P {ω | ∑ j ∈ s, X j ω < 1 / 4}).toReal
          ≤ (P (⋂ j ∈ s, {ω | X j ω < 1 / 4})).toReal :=
            ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
        _ = ∏ j ∈ s, (1 - p j) := by rw [hprod]; exact Finset.prod_congr rfl (fun j _ => hcompl j)
        _ ≤ ∏ j ∈ s, Real.exp (-p j) :=
            Finset.prod_le_prod (fun j _ => by
              have : p j ≤ 1 := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P))
              linarith) (fun j _ => by linarith [Real.add_one_le_exp (-p j)])
        _ = Real.exp (-∑ j ∈ s, p j) := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
        _ ≤ Real.exp (-(1 / 12 * (B - 16) / (m : ℝ))) :=
            Real.exp_le_exp.mpr (by linarith)
    · push_neg at hp_sum
      let X' : Fin n → Ω → ℝ := fun j ω => if X j ω < 1 / 4 then X j ω else 0
      have hX'm : ∀ j, Measurable (X' j) := fun j =>
        (hmeas j).ite (measurableSet_lt (hmeas j) measurable_const) measurable_const
      have hX'ind : iIndepFun X' P :=
        hind.comp (fun _ x => if x < 1 / 4 then x else 0)
          (fun _ => measurable_id.ite (measurableSet_lt measurable_id measurable_const) measurable_const)
      have hX'lt : ∀ j ω, 0 ≤ X' j ω ∧ X' j ω < 1 / 4 := fun j ω => by
        dsimp [X']; split_ifs with h
        · exact ⟨(hX j ω).1, h⟩
        · exact ⟨le_rfl, by norm_num⟩
      have hX'01 : ∀ j ω, 0 ≤ X' j ω ∧ X' j ω ≤ 1 := fun j ω =>
        ⟨(hX'lt j ω).1, by linarith [(hX'lt j ω).2]⟩
      set B' := ∑ j ∈ s, effSize P m (X' j)
      have hm_gt1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
      have hlogm_pos : 0 < Real.log m := Real.log_pos hm_gt1
      have hlog2_ge : (1 / 2 : ℝ) < Real.log 2 := by
        linarith [Real.log_two_gt_d9]
      have hlog2_le_m : Real.log 2 ≤ Real.log m :=
        Real.log_le_log zero_lt_two (by exact_mod_cast hm)
      have hm_ratio : ((m : ℝ) - 1) / Real.log m ≤ (m : ℝ) / Real.log 2 := by
        rw [div_le_div_iff₀ hlogm_pos (by linarith)]
        have : ((m : ℝ) - 1) * Real.log 2 ≤ (m : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have : (m : ℝ) * Real.log 2 ≤ (m : ℝ) * Real.log m :=
          mul_le_mul_of_nonneg_left hlog2_le_m hm_pos.le
        linarith
      have hB_le : B ≤ B' + 1 / 2 * (B - 16) := by
        have h1 : B ≤ B' + ((m : ℝ) - 1) / Real.log m * ∑ j ∈ s, p j := by
          calc B = ∑ j ∈ s, effSize P m (X j) := rfl
            _ ≤ ∑ j ∈ s, (effSize P m (X' j) + ((m : ℝ) - 1) / Real.log m * p j) :=
              Finset.sum_le_sum (fun j _ => effSize_le_trunc_add_prob P hm (X j) (hmeas j) (hX j))
            _ = B' + ((m : ℝ) - 1) / Real.log m * ∑ j ∈ s, p j := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hp_nn : 0 ≤ ∑ j ∈ s, p j := Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)
        have h2 : ((m : ℝ) - 1) / Real.log m * ∑ j ∈ s, p j ≤ 1 / 2 * (B - 16) := by
          calc ((m : ℝ) - 1) / Real.log m * ∑ j ∈ s, p j
              ≤ (m : ℝ) / Real.log 2 * (1 / 12 * (B - 16) / (m : ℝ)) := by
                apply mul_le_mul hm_ratio hp_sum.le hp_nn
                exact div_nonneg hm_pos.le (by linarith)
            _ = (1 / 12) / Real.log 2 * (B - 16) := by field_simp [hm_pos.ne']
            _ ≤ 1 / 2 * (B - 16) := by
                apply mul_le_mul_of_nonneg_right _ (by linarith)
                rw [div_le_iff₀ (by linarith)]
                linarith
        linarith
      have hB'_gt : 16 < B' := by linarith
      have hB_B' : B - 16 ≤ 2 * (B' - 16) := by linarith
      have hw : ∀ j ∈ s, 0 ≤ effSize P m (X' j) ∧ effSize P m (X' j) ≤ 1 := fun j _ =>
        effSize_nonneg_and_le P hm (X' j) (hX'm j) zero_le_one (hX'01 j)
      obtain ⟨r, f, hf_sub, hf_disj, hf_sum, hf_ub⟩ :=
        exists_disjoint_blocks s (fun j => effSize P m (X' j)) hw 2 zero_lt_two
      have hr_lb : (B - 16) / 6 ≤ (r : ℝ) := by
        have : B' ≤ (r : ℝ) * 3 + 2 := by linarith
        linarith
      have hsub_s : {ω | ∑ j ∈ s, X j ω < 1 / 4} ⊆
          ⋂ a ∈ (Finset.univ : Finset (Fin r)), {ω | ∑ j ∈ f a, X' j ω < 1 / 4} := by
        intro ω hω
        simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_setOf_eq] at hω ⊢
        intro a
        have h1 : ∑ j ∈ f a, X' j ω ≤ ∑ j ∈ s, X' j ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (hf_sub a) (fun j _ _ => (hX'lt j ω).1)
        have h2 : ∑ j ∈ s, X' j ω ≤ ∑ j ∈ s, X j ω := by
          apply Finset.sum_le_sum
          intro j _
          dsimp [X']; split_ifs
          · exact le_rfl
          · exact (hX j ω).1
        linarith
      have hprod_ind := disjoint_blocks_prod_indep P X' hX'm hX'ind f hf_disj (1 / 4) Finset.univ
      have hblock_le : ∀ a : Fin r,
          (P {ω | ∑ j ∈ f a, X' j ω < 1 / 4}).toReal ≤ Real.exp (-(1 / (2 * (m : ℝ)))) := by
        intro a
        have hgt := small_step_block_prob P hm X' hX'm hX'ind hX'lt (f a) (hf_sum a)
        have hmset : MeasurableSet {ω | ∑ j ∈ f a, X' j ω < 1 / 4} :=
          measurableSet_lt (Finset.measurable_sum _ (fun j _ => hX'm j)) measurable_const
        have hceq : {ω | ∑ j ∈ f a, X' j ω < 1 / 4}ᶜ = {ω | 1 / 4 ≤ ∑ j ∈ f a, X' j ω} := by
          ext ω; simp [not_lt]
        have hsum := measure_add_measure_compl hmset (μ := P)
        have hsum_real := congrArg ENNReal.toReal hsum
        rw [measure_univ, ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _),
          ENNReal.toReal_one, hceq] at hsum_real
        calc (P {ω | ∑ j ∈ f a, X' j ω < 1 / 4}).toReal
            = 1 - (P {ω | 1 / 4 ≤ ∑ j ∈ f a, X' j ω}).toReal := by linarith
          _ ≤ 1 - 1 / (2 * (m : ℝ)) := by linarith
          _ ≤ Real.exp (-(1 / (2 * (m : ℝ)))) := by
              linarith [Real.add_one_le_exp (-(1 / (2 * (m : ℝ))))]
      calc (P {ω | ∑ j ∈ s, X j ω < 1 / 4}).toReal
          ≤ (P (⋂ a ∈ (Finset.univ : Finset (Fin r)), {ω | ∑ j ∈ f a, X' j ω < 1 / 4})).toReal :=
            ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub_s)
        _ = ∏ a : Fin r, (P {ω | ∑ j ∈ f a, X' j ω < 1 / 4}).toReal := by
            rw [hprod_ind, ENNReal.toReal_prod]
        _ ≤ ∏ _a : Fin r, Real.exp (-(1 / (2 * (m : ℝ)))) :=
            Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun a _ => hblock_le a)
        _ = Real.exp (-((r : ℝ) * (1 / (2 * (m : ℝ))))) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
            congr 1; ring
        _ ≤ Real.exp (-(1 / 12 * (B - 16) / (m : ℝ))) := by
            apply Real.exp_le_exp.mpr
            rw [neg_le_neg_iff]
            calc 1 / 12 * (B - 16) / (m : ℝ)
                = (B - 16) / 6 * (1 / (2 * (m : ℝ))) := by ring
              _ ≤ (r : ℝ) * (1 / (2 * (m : ℝ))) :=
                  mul_le_mul_of_nonneg_right hr_lb (by positivity)

end StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory StochLoadBal.Makespan


lemma fiber_prod_indep {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (σ : Fin n → Fin m) (θ : ℝ) (S : Finset (Fin m)) :
    P (⋂ i ∈ S, {ω | ∑ j ∈ Finset.univ.filter (fun j => σ j = i), X j ω < θ}) =
      ∏ i ∈ S, P {ω | ∑ j ∈ Finset.univ.filter (fun j => σ j = i), X j ω < θ} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S haS ih =>
    rw [Finset.prod_insert haS, ← ih, Finset.set_biInter_insert]
    set F : Fin m → Finset (Fin n) := fun i => Finset.univ.filter (fun j => σ j = i) with hF
    set T : Finset (Fin n) := S.biUnion F with hT
    have hdisj : Disjoint (F a) T := by
      rw [Finset.disjoint_left]
      intro j hja hjT
      rw [hT, Finset.mem_biUnion] at hjT
      obtain ⟨i, hiS, hji⟩ := hjT
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hja hji
      exact haS (by rw [← hji, hja] at hiS; exact hiS)
    have hI := hind.indepFun_finset (F a) T hdisj hmeas
    apply hI.meas_inter
    · refine ⟨{v | ∑ j, v j < θ}, ?_, ?_⟩
      · exact measurableSet_lt (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
          measurable_const
      · ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        rw [Finset.sum_coe_sort (F a) (fun j => X j ω)]
    · let ext : (T → ℝ) → Fin n → ℝ := fun v j => if h : j ∈ T then v ⟨j, h⟩ else 0
      have hext : Measurable ext := by
        rw [measurable_pi_iff]
        intro j
        by_cases h : j ∈ T
        · simp only [ext, h, dite_true]
          exact measurable_pi_apply _
        · simp only [ext, h, dite_false]
          exact measurable_const
      refine ⟨{v | ∀ i ∈ S, ∑ j ∈ F i, ext v j < θ}, ?_, ?_⟩
      · have : {v : T → ℝ | ∀ i ∈ S, ∑ j ∈ F i, ext v j < θ} =
            ⋂ i ∈ S, {v | ∑ j ∈ F i, ext v j < θ} := by
          ext v; simp
        rw [this]
        refine Finset.measurableSet_biInter S (fun i _ => ?_)
        exact measurableSet_lt (Finset.measurable_sum _
          (fun j _ => (measurable_pi_apply j).comp hext)) measurable_const
      · ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iInter]
        apply forall₂_congr
        intro i hi
        have : ∑ j ∈ F i, ext (fun k : T => X k ω) j = ∑ j ∈ F i, X j ω := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjT : j ∈ T := by
            rw [hT, Finset.mem_biUnion]; exact ⟨i, hi, hj⟩
          simp [ext, hjT]
        rw [this]


lemma load_le_makespan {m n : ℕ} {Ω : Type} (X : Fin n → Ω → ℝ) (σ : Fin n → Fin m)
    (i : Fin m) (ω : Ω) :
    load (fun _ : Fin m => X) σ i ω ≤ makespan (fun _ : Fin m => X) σ ω :=
  le_ciSup (f := fun i => load (fun _ : Fin m => X) σ i ω) (Set.finite_range _).bddAbove i

theorem solution :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin n → Ω → ℝ),
        (∀ j, Measurable (X j)) → iIndepFun X P →
        (∀ j ω, 0 ≤ X j ω ∧ X j ω ≤ 1) →
        ∀ σ : Fin n → Fin m,
          17 * (m : ℝ) ≤ ∑ j, effSize P m (X j) →
          c₁ ≤ expMakespan P (fun _ : Fin m => X) σ := by
  classical
  obtain ⟨θ, c, hθ, hc, hKL⟩ := StochLoadBal.Makespan.lemma_4_group_tail_proved
  have hexp : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine ⟨min 1 (θ * (1 - Real.exp (-c))), lt_min one_pos (mul_pos hθ (by linarith)), ?_⟩
  intro m n hm Ω _ P _ X hmeas hind hX σ hsum
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hload_def : ∀ i ω, load (fun _ : Fin m => X) σ i ω =
      ∑ j ∈ Finset.univ.filter (fun j => σ j = i), X j ω := fun _ _ => rfl
  have hload_nonneg : ∀ i ω, 0 ≤ load (fun _ : Fin m => X) σ i ω := fun i ω =>
    Finset.sum_nonneg (fun j _ => (hX j ω).1)
  have hload_meas : ∀ i, Measurable (fun ω => load (fun _ : Fin m => X) σ i ω) := fun i =>
    Finset.measurable_sum _ (fun j _ => hmeas j)
  have hms_meas : Measurable (makespan (fun _ : Fin m => X) σ) := by
    unfold makespan; exact Measurable.iSup hload_meas
  have hms_nonneg : ∀ ω, 0 ≤ makespan (fun _ : Fin m => X) σ ω := fun ω =>
    (hload_nonneg ⟨0, hm⟩ ω).trans (load_le_makespan X σ _ ω)
  have hms_le : ∀ ω, makespan (fun _ : Fin m => X) σ ω ≤ n := by
    intro ω
    unfold makespan
    refine ciSup_le (fun i => ?_)
    calc load (fun _ : Fin m => X) σ i ω ≤ ∑ j, X j ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => (hX j ω).1)
      _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => (hX j ω).2)
      _ = n := by simp
  have hms_int : Integrable (makespan (fun _ : Fin m => X) σ) P :=
    Integrable.of_bound hms_meas.aestronglyMeasurable n (Filter.Eventually.of_forall
      (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hms_nonneg ω)]; exact hms_le ω))
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · -- the case `m = 1`: `β_1 = E` and the makespan is the total load
    have hm1 : m = 1 := by omega
    subst hm1
    simp only [effSize, if_true, Nat.cast_one, mul_one] at hsum
    have hXint : ∀ j, Integrable (X j) P := fun j =>
      Integrable.of_bound (hmeas j).aestronglyMeasurable 1 (Filter.Eventually.of_forall
        (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hX j ω).1]; exact (hX j ω).2))
    have hms_eq : ∀ ω, makespan (fun _ : Fin 1 => X) σ ω = ∑ j, X j ω := by
      intro ω
      unfold makespan
      rw [ciSup_unique, hload_def]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext j; simp [Subsingleton.elim (σ j) default]
    unfold expMakespan
    simp_rw [hms_eq]
    rw [integral_finset_sum _ (fun j _ => hXint j)]
    calc min 1 (θ * (1 - Real.exp (-c))) ≤ 1 := min_le_left _ _
      _ ≤ 17 := by norm_num
      _ ≤ _ := hsum
  · -- the case `m ≥ 2`
    set F : Fin m → Finset (Fin n) := fun i => Finset.univ.filter (fun j => σ j = i) with hF
    set B : Set Ω := ⋂ i ∈ (Finset.univ : Finset (Fin m)),
      {ω | ∑ j ∈ Finset.univ.filter (fun j => σ j = i), X j ω < θ} with hB
    have hBmeas : MeasurableSet B :=
      Finset.measurableSet_biInter _ (fun i _ => measurableSet_lt
        (Finset.measurable_sum _ (fun j _ => hmeas j)) measurable_const)
    have hPB : (P B).toReal ≤ Real.exp (-c) := by
      rw [hB, fiber_prod_indep P X hmeas hind σ θ Finset.univ, ENNReal.toReal_prod]
      calc ∏ i, (P {ω | ∑ j ∈ Finset.univ.filter (fun j => σ j = i), X j ω < θ}).toReal
          ≤ ∏ i : Fin m, Real.exp (-(c * (∑ j ∈ F i, effSize P m (X j) - 16) / m)) :=
            Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg)
              (fun i _ => hKL m n hm2 Ω P X hmeas hind hX (F i))
        _ = Real.exp (∑ i : Fin m, -(c * (∑ j ∈ F i, effSize P m (X j) - 16) / m)) :=
            (Real.exp_sum _ _).symm
        _ ≤ Real.exp (-c) := by
            apply Real.exp_le_exp.mpr
            have hfib : ∑ i : Fin m, ∑ j ∈ F i, effSize P m (X j) = ∑ j, effSize P m (X j) :=
              Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (σ j)) _
            have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
            have : ∑ i : Fin m, -(c * (∑ j ∈ F i, effSize P m (X j) - 16) / m) =
                -(c * (∑ j, effSize P m (X j) - 16 * m) / m) := by
              rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum,
                Finset.sum_sub_distrib, hfib]
              simp [mul_comm]
            rw [this, neg_le_neg_iff, le_div_iff₀ hmpos]
            nlinarith
    -- pointwise lower bound by `θ · 1_{Bᶜ}`
    have hpt : ∀ ω, Bᶜ.indicator (fun _ => θ) ω ≤ makespan (fun _ : Fin m => X) σ ω := by
      intro ω
      by_cases hω : ω ∈ Bᶜ
      · rw [Set.indicator_of_mem hω]
        simp only [hB, Set.mem_compl_iff, Set.mem_iInter, Set.mem_setOf_eq, not_forall,
          not_lt] at hω
        obtain ⟨i, _, hi⟩ := hω
        exact hi.trans ((hload_def i ω).symm ▸ load_le_makespan X σ i ω)
      · rw [Set.indicator_of_notMem hω]; exact hms_nonneg ω
    have hint_ind : ∫ ω, Bᶜ.indicator (fun _ => θ) ω ∂P = θ * (1 - (P B).toReal) := by
      rw [integral_indicator_const θ hBmeas.compl, smul_eq_mul, measureReal_def,
        prob_compl_eq_one_sub hBmeas, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one, mul_comm]
    have hmono : ∫ ω, Bᶜ.indicator (fun _ => θ) ω ∂P ≤ expMakespan P (fun _ : Fin m => X) σ :=
      integral_mono ((integrable_const θ).indicator hBmeas.compl) hms_int hpt
    calc min 1 (θ * (1 - Real.exp (-c))) ≤ θ * (1 - Real.exp (-c)) := min_le_right _ _
      _ ≤ θ * (1 - (P B).toReal) := by
          apply mul_le_mul_of_nonneg_left _ hθ.le; linarith
      _ = _ := hint_ind.symm
      _ ≤ _ := hmono
