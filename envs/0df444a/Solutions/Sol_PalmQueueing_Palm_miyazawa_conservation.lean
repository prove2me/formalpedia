-- Prove2me | solution 1 for PalmQueueing.Palm.miyazawa_conservation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:17:37.391489+00:00
-- url     : https://prove2.me/submissions/eae25dba-d72d-4c59-8735-7b496ec46cc0

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess



namespace PalmQueueing.Palm

open MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Basic facts about the counting measure -/

lemma lintegral_count (N : PointProcess Ω) (ω : Ω) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ t, g t ∂(N.count ω) = ∑' n : ℤ, g (N.T n ω) := by
  simp [PointProcess.count, lintegral_sum_measure, lintegral_dirac' _ hg]

lemma count_apply (N : PointProcess Ω) (ω : Ω) (C : Set ℝ) (hC : MeasurableSet C) :
    N.count ω C = ∑' n : ℤ, C.indicator (fun _ => (1:ℝ≥0∞)) (N.T n ω) := by
  simp [PointProcess.count, Measure.sum_apply _ hC, Measure.dirac_apply' _ hC]
  rfl

lemma measurable_shiftT (θ : Flow Ω) (N : PointProcess Ω) (n : ℤ) :
    Measurable fun ω => θ (N.T n ω) ω :=
  θ.measurable_uncurry.comp ((N.measurable_T n).prodMk measurable_id)

lemma measurable_pairT (θ : Flow Ω) (N : PointProcess Ω) (n : ℤ) :
    Measurable fun ω => (θ (N.T n ω) ω, N.T n ω) :=
  (measurable_shiftT θ N n).prodMk (N.measurable_T n)

lemma flow_add (θ : Flow Ω) (s t : ℝ) (ω : Ω) : θ s (θ t ω) = θ (s + t) ω := by
  have := θ.map_add s t
  exact (congrFun this ω).symm

lemma flow_zero (θ : Flow Ω) (ω : Ω) : θ 0 ω = ω := by
  have := θ.map_zero
  exact congrFun this ω

/-- the sum over points of a jointly measurable function -/
lemma lintegral_count_shift (S : PalmSetting Ω) (v : Ω → ℝ → ℝ≥0∞)
    (hv : Measurable (Function.uncurry v)) (ω : Ω) :
    ∫⁻ t, v (S.θ t ω) t ∂(S.N.count ω) = ∑' n : ℤ, v (S.θ (S.N.T n ω) ω) (S.N.T n ω) := by
  apply lintegral_count
  have : (fun t => v (S.θ t ω) t) = Function.uncurry v ∘ (fun t => (S.θ t ω, t)) := by
    ext t; rfl
  rw [this]
  exact hv.comp ((S.θ.measurable_uncurry.comp (measurable_id.prodMk measurable_const)).prodMk
    measurable_id)

lemma measurable_sumT (S : PalmSetting Ω) (v : Ω → ℝ → ℝ≥0∞)
    (hv : Measurable (Function.uncurry v)) :
    Measurable fun ω => ∑' n : ℤ, v (S.θ (S.N.T n ω) ω) (S.N.T n ω) := by
  apply Measurable.tsum
  intro n
  exact hv.comp (measurable_pairT S.θ S.N n)

/-- compatibility in map form -/
lemma count_shift_eq (S : PalmSetting Ω) (a : ℝ) (ω : Ω) :
    S.N.count (S.θ a ω) = Measure.map (fun s => s - a) (S.N.count ω) := by
  ext C hC
  rw [Measure.map_apply (measurable_sub_const a) hC]
  exact S.compatible a ω C hC

/-- The Campbell-type measure on `Ω × ℝ`. -/
noncomputable def campbellMeasure (S : PalmSetting Ω) : Measure (Ω × ℝ) :=
  Measure.sum fun n : ℤ => Measure.map (fun ω => (S.θ (S.N.T n ω) ω, S.N.T n ω)) S.P

lemma lintegral_campbellMeasure (S : PalmSetting Ω) (v : Ω → ℝ → ℝ≥0∞)
    (hv : Measurable (Function.uncurry v)) :
    ∫⁻ p, Function.uncurry v p ∂(campbellMeasure S)
      = ∫⁻ ω, ∑' n : ℤ, v (S.θ (S.N.T n ω) ω) (S.N.T n ω) ∂S.P := by
  unfold campbellMeasure
  rw [lintegral_sum_measure]
  rw [lintegral_tsum]
  · congr 1; ext n
    rw [lintegral_map hv (measurable_pairT S.θ S.N n)]
    rfl
  · intro n
    exact (hv.comp (measurable_pairT S.θ S.N n)).aemeasurable

/-- The function appearing in the Palm definition. -/
noncomputable def palmSum (S : PalmSetting Ω) (A : Set Ω) (C : Set ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℤ, C.indicator (fun _ => (1:ℝ≥0∞)) (S.N.T n ω) *
    A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ (S.N.T n ω) ω)

lemma measurable_indfun {A : Set Ω} (hA : MeasurableSet A) {C : Set ℝ} (hC : MeasurableSet C) :
    Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      C.indicator (fun _ => (1:ℝ≥0∞)) t * A.indicator (fun _ => (1:ℝ≥0∞)) ω) := by
  apply Measurable.mul
  · exact (measurable_const.indicator hC).comp measurable_snd
  · exact (measurable_const.indicator hA).comp measurable_fst

lemma palmSum_eq (S : PalmSetting Ω) {A : Set Ω} (hA : MeasurableSet A) {C : Set ℝ}
    (hC : MeasurableSet C) (ω : Ω) :
    palmSum S A C ω = ∫⁻ t, C.indicator (fun _ => (1:ℝ≥0∞)) t *
      A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ t ω) ∂(S.N.count ω) := by
  unfold palmSum
  rw [lintegral_count_shift S (fun ω t => C.indicator (fun _ => (1:ℝ≥0∞)) t *
      A.indicator (fun _ => (1:ℝ≥0∞)) ω) (measurable_indfun hA hC)]

lemma measurable_palmSum (S : PalmSetting Ω) {A : Set Ω} (hA : MeasurableSet A) {C : Set ℝ}
    (hC : MeasurableSet C) : Measurable (palmSum S A C) :=
  measurable_sumT S _ (measurable_indfun hA hC)

lemma palmSum_shift (S : PalmSetting Ω) {A : Set Ω} (hA : MeasurableSet A) (a t : ℝ) (ω : Ω) :
    palmSum S A (Set.Ioc 0 t) (S.θ a ω) = palmSum S A (Set.Ioc a (a + t)) ω := by
  rw [palmSum_eq S hA measurableSet_Ioc, palmSum_eq S hA measurableSet_Ioc, count_shift_eq]
  rw [lintegral_map _ (measurable_sub_const a)]
  · congr 1; ext u
    rw [flow_add]
    have h1 : u - a + a = u := by ring
    rw [h1]
    congr 1
    simp only [Set.indicator, Set.mem_Ioc]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  · exact (measurable_indfun hA measurableSet_Ioc).comp
      ((S.θ.measurable_uncurry.comp (measurable_id.prodMk measurable_const)).prodMk measurable_id)

lemma lintegral_palmSum_Ioc (S : PalmSetting Ω) {A : Set Ω} (hA : MeasurableSet A) (a b : ℝ)
    (hab : a < b) :
    ∫⁻ ω, palmSum S A (Set.Ioc a b) ω ∂S.P = ENNReal.ofReal (S.lam * (b - a)) * S.P0 A := by
  have h := S.palm.2 A hA (b - a) (by linarith)
  have h2 : ∀ ω, palmSum S A (Set.Ioc a b) ω = palmSum S A (Set.Ioc 0 (b - a)) (S.θ a ω) := by
    intro ω
    rw [palmSum_shift S hA]
    congr 2; ring
  simp_rw [h2]
  rw [← lintegral_map (measurable_palmSum S hA measurableSet_Ioc) (S.θ.measurable' a),
    S.invariant a, h]
  rfl

lemma campbellMeasure_prod (S : PalmSetting Ω) {A : Set Ω} (hA : MeasurableSet A) {C : Set ℝ}
    (hC : MeasurableSet C) :
    campbellMeasure S (A ×ˢ C) = ∫⁻ ω, palmSum S A C ω ∂S.P := by
  have h := lintegral_campbellMeasure S (fun ω t => C.indicator (fun _ => (1:ℝ≥0∞)) t *
      A.indicator (fun _ => (1:ℝ≥0∞)) ω) (measurable_indfun hA hC)
  rw [← lintegral_indicator_one (hA.prod hC)]
  convert h using 2
  · ext p
    simp only [Function.uncurry, Set.indicator, Set.mem_prod]
    by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ C <;> simp [h1, h2]
  · rfl

lemma campbellMeasure_prod_Ioc (S : PalmSetting Ω) {A : Set Ω} (hA : MeasurableSet A) (a b : ℝ)
    (hab : a < b) :
    campbellMeasure S (A ×ˢ Set.Ioc a b) = ENNReal.ofReal S.lam * S.P0 A * volume (Set.Ioc a b) := by
  rw [campbellMeasure_prod S hA measurableSet_Ioc, lintegral_palmSum_Ioc S hA a b hab,
    Real.volume_Ioc, ENNReal.ofReal_mul S.intensity.1.le]
  ring

lemma campbellMeasure_prod_eq (S : PalmSetting Ω) {A : Set Ω} (hA : MeasurableSet A) {C : Set ℝ}
    (hC : MeasurableSet C) :
    campbellMeasure S (A ×ˢ C) = ENNReal.ofReal S.lam * S.P0 A * volume C := by
  haveI := S.palm.1
  set ν : Measure ℝ := Measure.map Prod.snd ((campbellMeasure S).restrict (A ×ˢ Set.univ)) with hν
  have hνC : ∀ D : Set ℝ, MeasurableSet D → ν D = campbellMeasure S (A ×ˢ D) := by
    intro D hD
    rw [hν, Measure.map_apply measurable_snd hD, Measure.restrict_apply (measurable_snd hD)]
    congr 1
    ext p; simp [Set.mem_prod, and_comm]
  have hfin : ∀ ⦃a b : ℝ⦄, a < b → ν (Set.Ioc a b) ≠ ∞ := by
    intro a b hab
    rw [hνC _ measurableSet_Ioc, campbellMeasure_prod_Ioc S hA a b hab]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (by simp)
  have heq : ν = (ENNReal.ofReal S.lam * S.P0 A) • (volume : Measure ℝ) := by
    apply Measure.ext_of_Ioc' ν _ hfin
    intro a b hab
    rw [hνC _ measurableSet_Ioc, campbellMeasure_prod_Ioc S hA a b hab, Measure.smul_apply,
      smul_eq_mul]
  rw [← hνC C hC, heq, Measure.smul_apply, smul_eq_mul]

lemma campbellMeasure_eq (S : PalmSetting Ω) :
    campbellMeasure S = (ENNReal.ofReal S.lam • S.P0).prod (volume : Measure ℝ) := by
  haveI := S.palm.1
  haveI : IsFiniteMeasure (ENNReal.ofReal S.lam • S.P0) := Measure.smul_finite _ ENNReal.ofReal_ne_top
  symm
  apply Measure.prod_eq
  intro A C hA hC
  rw [campbellMeasure_prod_eq S hA hC, Measure.smul_apply, smul_eq_mul]

/-- **Mecke's formula**. -/
theorem mecke_core (S : PalmSetting Ω) (v : Ω → ℝ → ENNReal)
    (hv : Measurable (Function.uncurry v)) :
    ENNReal.ofReal S.lam * ∫⁻ ω, ∫⁻ t, v ω t ∂(volume : Measure ℝ) ∂S.P0
      = ∫⁻ ω, ∫⁻ t, v (S.θ t ω) t ∂(S.N.count ω) ∂S.P := by
  haveI := S.palm.1
  simp_rw [lintegral_count_shift S v hv]
  rw [← lintegral_campbellMeasure S v hv, campbellMeasure_eq, lintegral_prod _ hv.aemeasurable,
    lintegral_smul_measure]
  rfl

/-! ### Inversion formula -/

lemma T_pos_iff (N : PointProcess Ω) (ω : Ω) (n : ℤ) : 0 < N.T n ω ↔ 1 ≤ n := by
  constructor
  · intro h; by_contra hn; push_neg at hn
    have : N.T n ω ≤ N.T 0 ω := (N.strictMono ω).monotone (by omega)
    linarith [N.zero_le ω]
  · intro h; exact lt_of_lt_of_le (N.lt_one ω) ((N.strictMono ω).monotone h)

lemma count_eq_zero_iff (N : PointProcess Ω) (ω : Ω) (C : Set ℝ) (hC : MeasurableSet C) :
    N.count ω C = 0 ↔ ∀ n, N.T n ω ∉ C := by
  rw [count_apply N ω C hC, ENNReal.tsum_eq_zero]
  simp [Set.indicator_apply_eq_zero]

lemma nopoint_iff (N : PointProcess Ω) (ω : Ω) (s : ℝ) :
    (∀ n : ℤ, ¬ (0 < N.T n ω ∧ N.T n ω ≤ s)) ↔ s < N.T 1 ω := by
  constructor
  · intro h; by_contra hs; push_neg at hs
    exact h 1 ⟨N.lt_one ω, hs⟩
  · intro hs n ⟨h1, h2⟩
    have := (T_pos_iff N ω n).1 h1
    have := (N.strictMono ω).monotone this
    linarith

/-- the set `{(ω,t) : t ≤ 0, no point in (0,-t]}` -/
def invSet (N : PointProcess Ω) : Set (Ω × ℝ) :=
  {p | p.2 ≤ 0} ∩ ⋂ n : ℤ, {p | 0 < N.T n p.1 ∧ N.T n p.1 ≤ -p.2}ᶜ

lemma mem_invSet (N : PointProcess Ω) (p : Ω × ℝ) :
    p ∈ invSet N ↔ p.2 ≤ 0 ∧ ∀ n : ℤ, ¬ (0 < N.T n p.1 ∧ N.T n p.1 ≤ -p.2) := by
  simp [invSet]

lemma measurableSet_invSet (N : PointProcess Ω) : MeasurableSet (invSet N) := by
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_snd measurable_const
  · apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.compl
    exact (measurableSet_lt measurable_const ((N.measurable_T n).comp measurable_fst)).inter
      (measurableSet_le ((N.measurable_T n).comp measurable_fst) (measurable_neg.comp measurable_snd))

lemma shift_nopoint (S : PalmSetting Ω) (ω : Ω) (a : ℝ) :
    (∀ m : ℤ, ¬ (0 < S.N.T m (S.θ a ω) ∧ S.N.T m (S.θ a ω) ≤ -a)) ↔
      (∀ m : ℤ, ¬ (a < S.N.T m ω ∧ S.N.T m ω ≤ 0)) := by
  have h1 := count_eq_zero_iff S.N (S.θ a ω) (Set.Ioc 0 (-a)) measurableSet_Ioc
  have h2 := count_eq_zero_iff S.N ω (Set.Ioc a 0) measurableSet_Ioc
  have h3 : S.N.count (S.θ a ω) (Set.Ioc 0 (-a)) = S.N.count ω (Set.Ioc a 0) := by
    rw [S.compatible a ω _ measurableSet_Ioc]
    congr 1
    ext x; simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  simp only [Set.mem_Ioc] at h1 h2
  rw [← h1, h3, h2]

lemma invSet_term (S : PalmSetting Ω) (f : Ω → ℝ≥0∞) (ω : Ω) (n : ℤ) :
    (invSet S.N).indicator (fun p => f (S.θ (-p.2) p.1)) (S.θ (S.N.T n ω) ω, S.N.T n ω)
      = if n = 0 then f ω else 0 := by
  classical
  rw [Set.indicator_apply, mem_invSet, shift_nopoint]
  simp only
  by_cases hn : n = 0
  · subst hn
    rw [if_pos, if_pos rfl]
    · rw [flow_add]; simp [flow_zero]
    · refine ⟨S.N.zero_le ω, ?_⟩
      intro m ⟨h1, h2⟩
      have hm : 0 < m := (S.N.strictMono ω).lt_iff_lt.1 h1
      have := (S.N.strictMono ω).monotone (show 1 ≤ m by omega)
      linarith [S.N.lt_one ω]
  · rw [if_neg hn, if_neg]
    intro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact h2 0 ⟨(S.N.strictMono ω) hn, S.N.zero_le ω⟩
    · have := (S.N.strictMono ω).monotone (show 1 ≤ n by omega)
      linarith [S.N.lt_one ω]

lemma measurable_invF (S : PalmSetting Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    Measurable ((invSet S.N).indicator (fun p : Ω × ℝ => f (S.θ (-p.2) p.1))) := by
  apply Measurable.indicator _ (measurableSet_invSet S.N)
  exact hf.comp (S.θ.measurable_uncurry.comp ((measurable_neg.comp measurable_snd).prodMk
    measurable_fst))

lemma inv_inner (S : PalmSetting Ω) (f : Ω → ℝ≥0∞) (ω : Ω) :
    ∫⁻ t, (invSet S.N).indicator (fun p : Ω × ℝ => f (S.θ (-p.2) p.1)) (ω, t)
        ∂(volume : Measure ℝ)
      = ∫⁻ t in Set.Ioc (0:ℝ) (S.N.T 1 ω), f (S.θ t ω) ∂(volume : Measure ℝ) := by
  classical
  rw [← lintegral_neg_eq_self]
  rw [← Measure.restrict_congr_set Ico_ae_eq_Ioc, ← lintegral_indicator measurableSet_Ico]
  congr 1; ext t
  rw [Set.indicator_apply, Set.indicator_apply, mem_invSet]
  simp only [neg_neg, Set.mem_Ico]
  by_cases h : 0 ≤ t ∧ t < S.N.T 1 ω
  · rw [if_pos h, if_pos]
    refine ⟨by linarith [h.1], ?_⟩
    exact (nopoint_iff S.N ω t).2 h.2
  · rw [if_neg h, if_neg]
    intro ⟨h1, h2⟩
    exact h ⟨by linarith, (nopoint_iff S.N ω t).1 h2⟩

/-- **Inversion formula**. -/
theorem inversion_core (S : PalmSetting Ω) (f : Ω → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂S.P
      = ENNReal.ofReal S.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S.N.T 1 ω), f (S.θ t ω) ∂(volume : Measure ℝ) ∂S.P0 := by
  have hv : Measurable (Function.uncurry fun ω t =>
      (invSet S.N).indicator (fun p : Ω × ℝ => f (S.θ (-p.2) p.1)) (ω, t)) := by
    have : (Function.uncurry fun ω t =>
        (invSet S.N).indicator (fun p : Ω × ℝ => f (S.θ (-p.2) p.1)) (ω, t))
        = (invSet S.N).indicator (fun p : Ω × ℝ => f (S.θ (-p.2) p.1)) := by ext ⟨a, b⟩; rfl
    rw [this]; exact measurable_invF S f hf
  have h := mecke_core S _ hv
  simp_rw [inv_inner] at h
  rw [h]
  congr 1; ext ω
  rw [lintegral_count_shift S _ hv]
  simp_rw [invSet_term]
  simp

/-! ### Mean value formulas -/

lemma lam_pos (S : PalmSetting Ω) : ENNReal.ofReal S.lam ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact S.intensity.1

lemma lam_ET1 (S : PalmSetting Ω) :
    ENNReal.ofReal S.lam * ∫⁻ ω, ENNReal.ofReal (S.N.T 1 ω) ∂S.P0 = 1 := by
  haveI := S.isProb
  have h := inversion_core S (fun _ => 1) measurable_const
  simp only [lintegral_const, measure_univ, one_mul] at h
  rw [h]
  congr 1
  apply lintegral_congr
  intro ω
  rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

lemma count_Ioc01 (S : PalmSetting Ω) :
    ∫⁻ ω, ∑' n : ℤ, Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ENNReal)) (S.N.T n ω) ∂S.P
      = ENNReal.ofReal S.lam := by
  rw [S.intensity.2]
  congr 1; ext ω
  rw [count_apply S.N ω _ measurableSet_Ioc]

lemma indicator_const_mul {α : Type*} (C : Set α) (c : ℝ≥0∞) (x : α) :
    C.indicator (fun _ => c) x = c * C.indicator (fun _ => (1:ℝ≥0∞)) x := by
  classical
  simp only [Set.indicator_apply]; split_ifs <;> simp

theorem mean_value_core {K : Type*} [MeasurableSpace K] (S : PalmSetting Ω)
    (Z : ℝ → Ω → K) (hZmeas : ∀ t, Measurable (Z t))
    (hZ : ∀ (t : ℝ) (ω : Ω), Z t ω = Z 0 (S.θ t ω))
    (g : K → ENNReal) (hg : Measurable g) :
    (∫⁻ ω, g (Z 0 ω) ∂S.P
        = (∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S.N.T 1 ω), g (Z t ω) ∂(volume : Measure ℝ) ∂S.P0)
            / (∫⁻ ω, ENNReal.ofReal (S.N.T 1 ω) ∂S.P0))
      ∧ (∫⁻ ω, g (Z 0 ω) ∂S.P0
        = (∫⁻ ω, ∑' n : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => g (Z (S.N.T n ω) ω)) (S.N.T n ω) ∂S.P)
            / (∫⁻ ω, ∑' n : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ENNReal)) (S.N.T n ω) ∂S.P)) := by
  haveI := S.isProb
  haveI := S.palm.1
  constructor
  · have h := inversion_core S (fun ω => g (Z 0 ω)) (hg.comp (hZmeas 0))
    simp_rw [← hZ] at h
    rw [h]
    have hD := lam_ET1 S
    have : (∫⁻ ω, ENNReal.ofReal (S.N.T 1 ω) ∂S.P0)⁻¹ = ENNReal.ofReal S.lam := by
      rw [← ENNReal.eq_inv_of_mul_eq_one_left hD]
    rw [div_eq_mul_inv, this, mul_comm]
  · rw [count_Ioc01]
    have hv : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        g (Z 0 ω) * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t) := by
      apply Measurable.mul
      · exact (hg.comp (hZmeas 0)).comp measurable_fst
      · exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
    have h := mecke_core S _ hv
    have h1 : ∀ ω, ∫⁻ t, g (Z 0 ω) * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t
        ∂(volume : Measure ℝ) = g (Z 0 ω) := by
      intro ω
      rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Ioc),
        lintegral_indicator_const measurableSet_Ioc]
      simp
    simp_rw [h1] at h
    have h2 : ∀ ω, ∫⁻ t, g (Z 0 (S.θ t ω)) * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t
        ∂(S.N.count ω) = ∑' n : ℤ,
          Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => g (Z (S.N.T n ω) ω)) (S.N.T n ω) := by
      intro ω
      rw [lintegral_count_shift S _ hv]
      congr 1; ext n
      rw [indicator_const_mul (Set.Ioc 0 1) (g (Z (S.N.T n ω) ω)), hZ (S.N.T n ω) ω]
    simp_rw [h2] at h
    rw [← h, mul_comm, ENNReal.mul_div_cancel_right (lam_pos S) ENNReal.ofReal_ne_top]

/-! ### Miyazawa's rate conservation principle -/

lemma measurable_flow_at (θ : Flow Ω) (ω : Ω) : Measurable fun t : ℝ => θ t ω :=
  θ.measurable_uncurry.comp (measurable_id.prodMk measurable_const)

lemma count_Ioc_lt_top (N : PointProcess Ω) (ω : Ω) (a b : ℝ) :
    N.count ω (Set.Ioc a b) < ⊤ := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((N.tendsto_atTop ω).eventually (eventually_gt_atTop b))
  obtain ⟨m, hm⟩ := eventually_atBot.1 ((N.tendsto_atBot ω).eventually (eventually_le_atBot a))
  rw [count_apply N ω _ measurableSet_Ioc]
  rw [tsum_eq_sum (s := Finset.Icc m M)]
  · exact ENNReal.sum_lt_top.2 (fun n _ => by
      rw [Set.indicator_apply]; split_ifs <;> simp)
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_Ioc, not_and, not_le]
    intro h1
    rcases hn with hn | hn
    · have := hm n hn.le; linarith
    · have := hM n hn.le; linarith

lemma leftLimit_compatible (θ : Flow Ω) (Y Yl : ℝ → Ω → ℝ) (hYleft : IsLeftLimitProcess Y Yl)
    (hYcomp : IsCompatible θ Y) (s : ℝ) (ω : Ω) : Yl s ω = Yl 0 (θ s ω) := by
  have h1 := hYleft s ω
  have h2 := hYleft 0 (θ s ω)
  have h3 : Tendsto (fun u : ℝ => u + s) (nhdsWithin 0 (Set.Iio 0)) (nhdsWithin s (Set.Iio s)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun u : ℝ => u + s) (nhds 0) (nhds (0 + s)) :=
        (continuous_add_right s).tendsto 0
      rw [zero_add] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [Set.mem_Iio] at hu ⊢; linarith
  have h4 : Tendsto (fun u => Y u (θ s ω)) (nhdsWithin 0 (Set.Iio 0)) (nhds (Yl s ω)) := by
    have : (fun u => Y u (θ s ω)) = (fun u => Y u ω) ∘ (fun u => u + s) := by
      ext u; exact hYcomp u s ω
    rw [this]; exact h1.comp h3
  exact (tendsto_nhds_unique h2 h4).symm

lemma leftLimit_bdd (Y Yl : ℝ → Ω → ℝ) (hYleft : IsLeftLimitProcess Y Yl) (C : ℝ)
    (hC : ∀ t ω, |Y t ω| ≤ C) (s : ℝ) (ω : Ω) : |Yl s ω| ≤ C := by
  have h : Tendsto (fun u => |Y u ω|) (nhdsWithin s (Set.Iio s)) (nhds |Yl s ω|) :=
    (continuous_abs.tendsto _).comp (hYleft s ω)
  exact le_of_tendsto' h (fun u => hC u ω)

theorem miyazawa_core (S : PalmSetting Ω) (Y Yl Y' : ℝ → Ω → ℝ)
    (hYbdd : ∃ C : ℝ, ∀ (t : ℝ) (ω : Ω), |Y t ω| ≤ C)
    (hYmeas : ∀ t, Measurable (Y t)) (hYlmeas : ∀ t, Measurable (Yl t))
    (hY'meas : ∀ t, Measurable (Y' t)) (hY'int : Integrable (Y' 0) S.P)
    (hYright : ∀ (s : ℝ) (ω : Ω), ContinuousWithinAt (fun u => Y u ω) (Set.Ici s) s)
    (hYleft : IsLeftLimitProcess Y Yl)
    (hYcomp : IsCompatible S.θ Y) (hY'comp : IsCompatible S.θ Y')
    (hjump : ∀ ω, Y 1 ω = Y 0 ω + (∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ))
        + ∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)) :
    (∫ ω, Y' 0 ω ∂S.P) + S.lam * ∫ ω, (Y 0 ω - Yl 0 ω) ∂S.P0 = 0 := by
  haveI := S.isProb
  haveI := S.palm.1
  obtain ⟨C, hC⟩ := hYbdd
  have hYc : ∀ s ω, Y s ω = Y 0 (S.θ s ω) := fun s ω => by rw [hYcomp 0 s ω, zero_add]
  have hY'c : ∀ s ω, Y' s ω = Y' 0 (S.θ s ω) := fun s ω => by rw [hY'comp 0 s ω, zero_add]
  have hYlc : ∀ s ω, Yl s ω = Yl 0 (S.θ s ω) := leftLimit_compatible S.θ Y Yl hYleft hYcomp
  have hCl := leftLimit_bdd Y Yl hYleft C hC
  -- stationarity of Y
  have hEY : ∫ ω, Y 1 ω ∂S.P = ∫ ω, Y 0 ω ∂S.P := by
    have : (fun ω => Y 1 ω) = fun ω => Y 0 (S.θ 1 ω) := by ext ω; rw [hYc 1 ω]
    rw [this, ← integral_map (S.θ.measurable' 1).aemeasurable (hYmeas 0).aestronglyMeasurable,
      S.invariant 1]
  -- the drift term
  have hg : Measurable fun p : Ω × ℝ => Y' p.2 p.1 := by
    have : (fun p : Ω × ℝ => Y' p.2 p.1) = fun p => Y' 0 (S.θ p.2 p.1) := by
      ext p; rw [hY'c]
    rw [this]
    exact (hY'meas 0).comp (S.θ.measurable_uncurry.comp (measurable_snd.prodMk measurable_fst))
  have hgint : Integrable (fun p : Ω × ℝ => Y' p.2 p.1)
      (S.P.prod ((volume : Measure ℝ).restrict (Set.Ioc 0 1))) := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (hg.enorm).aemeasurable]
    simp only
    rw [lintegral_lintegral_swap]
    · have e1 : ∀ s, ∫⁻ ω, ‖Y' s ω‖ₑ ∂S.P = ∫⁻ ω, ‖Y' 0 ω‖ₑ ∂S.P := by
        intro s
        simp_rw [hY'c s]
        rw [← lintegral_map (hY'meas 0).enorm (S.θ.measurable' s), S.invariant s]
      simp_rw [e1]
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_one, mul_one]
      exact hY'int.hasFiniteIntegral
    · exact (hg.enorm).aemeasurable
  have hI1int : Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ)) S.P :=
    hgint.integral_prod_left
  have hI1 : ∫ ω, (∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ)) ∂S.P
      = ∫ ω, Y' 0 ω ∂S.P := by
    rw [integral_integral_swap hgint]
    have e1 : ∀ s, ∫ ω, Y' s ω ∂S.P = ∫ ω, Y' 0 ω ∂S.P := by
      intro s
      simp_rw [hY'c s]
      rw [← integral_map (S.θ.measurable' s).aemeasurable (hY'meas 0).aestronglyMeasurable,
        S.invariant s]
    simp_rw [e1]
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one,
      one_smul]
  -- the jump term
  set vP : Ω → ℝ → ℝ≥0∞ := fun ω s =>
    (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) s * ENNReal.ofReal (Y 0 ω - Yl 0 ω) with hvP
  set vM : Ω → ℝ → ℝ≥0∞ := fun ω s =>
    (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) s * ENNReal.ofReal (Yl 0 ω - Y 0 ω) with hvM
  have hvPm : Measurable (Function.uncurry vP) :=
    ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd).mul
      (((hYmeas 0).sub (hYlmeas 0)).ennreal_ofReal.comp measurable_fst)
  have hvMm : Measurable (Function.uncurry vM) :=
    ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd).mul
      (((hYlmeas 0).sub (hYmeas 0)).ennreal_ofReal.comp measurable_fst)
  have hinnerP : ∀ ω, ∫⁻ s, vP ω s ∂(volume : Measure ℝ) = ENNReal.ofReal (Y 0 ω - Yl 0 ω) := by
    intro ω
    simp only [hvP]
    rw [lintegral_mul_const _ (measurable_const.indicator measurableSet_Ioc),
      lintegral_indicator_const measurableSet_Ioc]
    simp
  have hinnerM : ∀ ω, ∫⁻ s, vM ω s ∂(volume : Measure ℝ) = ENNReal.ofReal (Yl 0 ω - Y 0 ω) := by
    intro ω
    simp only [hvM]
    rw [lintegral_mul_const _ (measurable_const.indicator measurableSet_Ioc),
      lintegral_indicator_const measurableSet_Ioc]
    simp
  have hMP := mecke_core S vP hvPm
  have hMM := mecke_core S vM hvMm
  simp_rw [hinnerP] at hMP
  simp_rw [hinnerM] at hMM
  -- the pointwise decomposition of the jump integral
  have hdec : ∀ ω, ∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)
      = (∫⁻ s, vP (S.θ s ω) s ∂(S.N.count ω)).toReal
        - (∫⁻ s, vM (S.θ s ω) s ∂(S.N.count ω)).toReal := by
    intro ω
    haveI : IsFiniteMeasure ((S.N.count ω).restrict (Set.Ioc (0:ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact count_Ioc_lt_top S.N ω 0 1⟩
    have hfm : Measurable fun s => Y s ω - Yl s ω := by
      have : (fun s => Y s ω - Yl s ω) = fun s => Y 0 (S.θ s ω) - Yl 0 (S.θ s ω) := by
        ext s; rw [hYc s ω, hYlc s ω]
      rw [this]
      exact ((hYmeas 0).comp (measurable_flow_at S.θ ω)).sub
        ((hYlmeas 0).comp (measurable_flow_at S.θ ω))
    have hfi : Integrable (fun s => Y s ω - Yl s ω) ((S.N.count ω).restrict (Set.Ioc (0:ℝ) 1)) := by
      refine Integrable.mono' (integrable_const (C + C)) hfm.aestronglyMeasurable ?_
      filter_upwards with s
      rw [Real.norm_eq_abs]
      calc |Y s ω - Yl s ω| ≤ |Y s ω| + |Yl s ω| := abs_sub _ _
        _ ≤ C + C := add_le_add (hC s ω) (hCl s ω)
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    congr 2
    · rw [← lintegral_indicator measurableSet_Ioc]
      congr 1; ext s
      simp only [hvP, Set.indicator_apply, Set.mem_Ioc, hYc s ω, hYlc s ω]
      split_ifs <;> simp
    · rw [← lintegral_indicator measurableSet_Ioc]
      congr 1; ext s
      simp only [hvM, Set.indicator_apply, Set.mem_Ioc, hYc s ω, hYlc s ω]
      split_ifs <;> simp [neg_sub]
  -- integrability of the two parts
  have hLPm : Measurable fun ω => ∫⁻ s, vP (S.θ s ω) s ∂(S.N.count ω) := by
    simp_rw [lintegral_count_shift S vP hvPm]; exact measurable_sumT S vP hvPm
  have hLMm : Measurable fun ω => ∫⁻ s, vM (S.θ s ω) s ∂(S.N.count ω) := by
    simp_rw [lintegral_count_shift S vM hvMm]; exact measurable_sumT S vM hvMm
  have hbP : ∫⁻ ω, ENNReal.ofReal (Y 0 ω - Yl 0 ω) ∂S.P0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (C + C) ∂S.P0) (by simp) ?_
    apply lintegral_mono; intro ω
    apply ENNReal.ofReal_le_ofReal
    linarith [(abs_le.1 (hC 0 ω)).2, (abs_le.1 (hCl 0 ω)).1]
  have hbM : ∫⁻ ω, ENNReal.ofReal (Yl 0 ω - Y 0 ω) ∂S.P0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (C + C) ∂S.P0) (by simp) ?_
    apply lintegral_mono; intro ω
    apply ENNReal.ofReal_le_ofReal
    linarith [(abs_le.1 (hC 0 ω)).1, (abs_le.1 (hCl 0 ω)).2]
  have hLPfin : ∫⁻ ω, ∫⁻ s, vP (S.θ s ω) s ∂(S.N.count ω) ∂S.P ≠ ⊤ := by
    rw [← hMP]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbP
  have hLMfin : ∫⁻ ω, ∫⁻ s, vM (S.θ s ω) s ∂(S.N.count ω) ∂S.P ≠ ⊤ := by
    rw [← hMM]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbM
  have hLPint := integrable_toReal_of_lintegral_ne_top hLPm.aemeasurable hLPfin
  have hLMint := integrable_toReal_of_lintegral_ne_top hLMm.aemeasurable hLMfin
  have hI2int : Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)) S.P := by
    simp_rw [hdec]; exact hLPint.sub hLMint
  have hI2 : ∫ ω, (∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)) ∂S.P
      = S.lam * ∫ ω, (Y 0 ω - Yl 0 ω) ∂S.P0 := by
    simp_rw [hdec]
    rw [integral_sub hLPint hLMint, integral_toReal hLPm.aemeasurable (ae_lt_top hLPm hLPfin),
      integral_toReal hLMm.aemeasurable (ae_lt_top hLMm hLMfin), ← hMP, ← hMM]
    have hfi0 : Integrable (fun ω => Y 0 ω - Yl 0 ω) S.P0 := by
      refine Integrable.mono' (integrable_const (C + C)) ((hYmeas 0).sub (hYlmeas 0)).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      calc |Y 0 ω - Yl 0 ω| ≤ |Y 0 ω| + |Yl 0 ω| := abs_sub _ _
        _ ≤ C + C := add_le_add (hC 0 ω) (hCl 0 ω)
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi0]
    simp_rw [neg_sub]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal S.intensity.1.le]
    ring
  -- Y 0 integrable
  have hY0int : Integrable (Y 0) S.P := by
    refine Integrable.mono' (integrable_const C) (hYmeas 0).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]; exact hC 0 ω
  -- integrate the jump identity
  have hsum : ∫ ω, Y 1 ω ∂S.P = ∫ ω, Y 0 ω ∂S.P
      + ∫ ω, (∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ)) ∂S.P
      + ∫ ω, (∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)) ∂S.P := by
    simp_rw [hjump]
    have hA : Integrable (fun ω => Y 0 ω + ∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ))
      S.P := hY0int.add hI1int
    rw [integral_add hA hI2int, integral_add hY0int hI1int]
  rw [hEY, hI1, hI2] at hsum
  linarith

end PalmQueueing.Palm

open PalmQueueing.Palm
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (S : PalmSetting Ω) (Y Yl Y' : ℝ → Ω → ℝ)
    (hYbdd : ∃ C : ℝ, ∀ (t : ℝ) (ω : Ω), |Y t ω| ≤ C)
    (hYmeas : ∀ t, Measurable (Y t)) (hYlmeas : ∀ t, Measurable (Yl t))
    (hY'meas : ∀ t, Measurable (Y' t)) (hY'int : Integrable (Y' 0) S.P)
    (hYright : ∀ (s : ℝ) (ω : Ω), ContinuousWithinAt (fun u => Y u ω) (Set.Ici s) s)
    (hYleft : IsLeftLimitProcess Y Yl)
    (hYcomp : IsCompatible S.θ Y) (hY'comp : IsCompatible S.θ Y')
    (hjump : ∀ ω, Y 1 ω = Y 0 ω + (∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ))
        + ∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)) :
    (∫ ω, Y' 0 ω ∂S.P) + S.lam * ∫ ω, (Y 0 ω - Yl 0 ω) ∂S.P0 = 0 := by
  exact miyazawa_core S Y Yl Y' hYbdd hYmeas hYlmeas hY'meas hY'int hYright hYleft hYcomp hY'comp hjump
