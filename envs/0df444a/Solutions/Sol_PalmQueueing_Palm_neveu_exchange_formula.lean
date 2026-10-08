-- Prove2me | solution 1 for PalmQueueing.Palm.neveu_exchange_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:10:25.883598+00:00
-- url     : https://prove2.me/submissions/c603d079-a89a-4bf8-83d8-46670d0c007e

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.3.4): the Neveu exchange formula (§1.3.2, p.21)
-/


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

/-! ### Relabeling of the points under the flow -/

lemma count_singleton_ne_zero_iff (N : PointProcess Ω) (ω : Ω) (x : ℝ) :
    N.count ω {x} ≠ 0 ↔ ∃ n, N.T n ω = x := by
  rw [Ne, count_eq_zero_iff N ω {x} (measurableSet_singleton x)]
  push_neg
  simp

lemma range_shift (S : PalmSetting Ω) (ω : Ω) (s x : ℝ) :
    (∃ k, S.N.T k (S.θ s ω) = x) ↔ ∃ n, S.N.T n ω = x + s := by
  rw [← count_singleton_ne_zero_iff, ← count_singleton_ne_zero_iff,
    S.compatible s ω _ (measurableSet_singleton x)]
  have : ((fun u => u - s) ⁻¹' {x}) = {x + s} := by
    ext u; simp [sub_eq_iff_eq_add]
  rw [this]

lemma succ_step {f g : ℤ → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    (hr : ∀ x, (∃ k, f k = x) ↔ (∃ k, g k = x)) (k : ℤ) (hk : f k = g k) :
    f (k + 1) = g (k + 1) := by
  obtain ⟨j, hj⟩ := (hr (f (k + 1))).1 ⟨_, rfl⟩
  have hjk : k < j := hg.lt_iff_lt.1 (by rw [hj, ← hk]; exact hf (lt_add_one k))
  by_contra hne
  have hne' : j ≠ k + 1 := by
    intro h; subst h; exact hne hj.symm
  have hlt : k + 1 < j := lt_of_le_of_ne (by omega) (Ne.symm hne')
  obtain ⟨i, hi⟩ := (hr (g (k + 1))).2 ⟨_, rfl⟩
  have h1 : k < i := hf.lt_iff_lt.1 (by rw [hi, hk]; exact hg (lt_add_one k))
  have h2 : i < k + 1 := hf.lt_iff_lt.1 (by rw [hi, ← hj]; exact hg hlt)
  omega

lemma pred_step {f g : ℤ → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    (hr : ∀ x, (∃ k, f k = x) ↔ (∃ k, g k = x)) (k : ℤ) (hk : f k = g k) :
    f (k - 1) = g (k - 1) := by
  obtain ⟨j, hj⟩ := (hr (f (k - 1))).1 ⟨_, rfl⟩
  have hjk : j < k := hg.lt_iff_lt.1 (by rw [hj, ← hk]; exact hf (by omega))
  by_contra hne
  have hne' : j ≠ k - 1 := by
    intro h; subst h; exact hne hj.symm
  have hlt : j < k - 1 := lt_of_le_of_ne (by omega) hne'
  obtain ⟨i, hi⟩ := (hr (g (k - 1))).2 ⟨_, rfl⟩
  have h1 : i < k := hf.lt_iff_lt.1 (by rw [hi, hk]; exact hg (by omega))
  have h2 : k - 1 < i := hf.lt_iff_lt.1 (by rw [hi, ← hj]; exact hg hlt)
  omega

lemma strictMono_range_eq {f g : ℤ → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    (hr : ∀ x, (∃ k, f k = x) ↔ (∃ k, g k = x))
    (hf0 : f 0 ≤ 0) (hf1 : 0 < f 1) (hg0 : g 0 ≤ 0) (hg1 : 0 < g 1) : f = g := by
  have h0 : f 0 = g 0 := by
    obtain ⟨j, hj⟩ := (hr (f 0)).1 ⟨_, rfl⟩
    obtain ⟨i, hi⟩ := (hr (g 0)).2 ⟨_, rfl⟩
    have hj1 : j < 1 := hg.lt_iff_lt.1 (by rw [hj]; linarith)
    have hi1 : i < 1 := hf.lt_iff_lt.1 (by rw [hi]; linarith)
    rcases lt_or_eq_of_le (show j ≤ 0 by omega) with hj0 | hj0
    · have h1 : g j < g 0 := hg hj0
      have h2 : f i ≤ f 0 := hf.monotone (by omega)
      linarith
    · subst hj0; exact hj.symm
  funext k
  induction k using Int.induction_on with
  | zero => exact h0
  | succ n ih => exact succ_step hf hg hr n ih
  | pred n ih => exact pred_step hf hg hr (-(n:ℤ)) ih

lemma exists_cycle (N : PointProcess Ω) (ω : Ω) (s : ℝ) :
    ∃ m : ℤ, N.T m ω ≤ s ∧ s < N.T (m + 1) ω := by
  have hinh : ∃ z : ℤ, N.T z ω ≤ s := by
    have := (N.tendsto_atBot ω).eventually (eventually_le_atBot s)
    exact this.exists
  have hbdd : ∃ b : ℤ, ∀ z, N.T z ω ≤ s → z ≤ b := by
    have := (N.tendsto_atTop ω).eventually (eventually_gt_atTop s)
    obtain ⟨b, hb⟩ := eventually_atTop.1 this
    refine ⟨b, fun z hz => ?_⟩
    by_contra h; push_neg at h
    have := hb z h.le
    linarith
  obtain ⟨m, hm, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  refine ⟨m, hm, ?_⟩
  by_contra h; push_neg at h
  have := hmax (m + 1) h
  omega

lemma exists_cycle' (N : PointProcess Ω) (ω : Ω) (s : ℝ) :
    ∃ m : ℤ, N.T m ω < s ∧ s ≤ N.T (m + 1) ω := by
  have hinh : ∃ z : ℤ, N.T z ω < s := by
    have := (N.tendsto_atBot ω).eventually (eventually_lt_atBot s)
    exact this.exists
  have hbdd : ∃ b : ℤ, ∀ z, N.T z ω < s → z ≤ b := by
    have := (N.tendsto_atTop ω).eventually (eventually_ge_atTop s)
    obtain ⟨b, hb⟩ := eventually_atTop.1 this
    refine ⟨b, fun z hz => ?_⟩
    by_contra h; push_neg at h
    have := hb z h.le
    linarith
  obtain ⟨m, hm, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  refine ⟨m, hm, ?_⟩
  by_contra h; push_neg at h
  have := hmax (m + 1) h
  omega

/-- **Relabeling**: the points of `θ_s ω` are `T_{m+k}(ω) - s`. -/
lemma shift_T (S : PalmSetting Ω) (ω : Ω) (s : ℝ) (m : ℤ) (hm : S.N.T m ω ≤ s ∧ s < S.N.T (m + 1) ω)
    (k : ℤ) : S.N.T k (S.θ s ω) = S.N.T (m + k) ω - s := by
  have hf : StrictMono fun k => S.N.T (m + k) ω - s := by
    intro a b hab
    simp only
    have := S.N.strictMono ω (show m + a < m + b by omega)
    linarith
  have := strictMono_range_eq hf (S.N.strictMono (S.θ s ω)) ?_ ?_ ?_ (S.N.zero_le _) (S.N.lt_one _)
  · exact (congrFun this k).symm
  · intro x
    rw [range_shift]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨m + k, by linarith⟩
    · rintro ⟨n, hn⟩
      exact ⟨n - m, by show S.N.T (m + (n - m)) ω - s = x; rw [show m + (n - m) = n by ring]; linarith⟩
  · show S.N.T (m + 0) ω - s ≤ 0
    rw [add_zero]; linarith [hm.1]
  · show 0 < S.N.T (m + 1) ω - s
    linarith [hm.2]

lemma shift_T_at (S : PalmSetting Ω) (ω : Ω) (n k : ℤ) :
    S.N.T k (S.θ (S.N.T n ω) ω) = S.N.T (n + k) ω - S.N.T n ω :=
  shift_T S ω _ n ⟨le_rfl, S.N.strictMono ω (lt_add_one n)⟩ k

/-! ### Invariance of the Palm probability under the point shift -/

lemma inner_shift_indicator (c : ℝ) :
    ∫⁻ t, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (c + t) ∂(volume : Measure ℝ) = 1 := by
  rw [lintegral_add_left_eq_self (fun t => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t) c,
    lintegral_indicator_const measurableSet_Ioc]
  simp

theorem palm_invariant_core (S : PalmSetting Ω)
    (hshift : Measurable fun ω => S.θ (S.N.T 1 ω) ω) :
    Measure.map (fun ω => S.θ (S.N.T 1 ω) ω) S.P0 = S.P0 := by
  haveI := S.palm.1
  ext A hA
  rw [Measure.map_apply hshift hA]
  -- first Mecke
  have hv1 : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      A.indicator (fun _ => (1:ℝ≥0∞)) ω *
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (S.N.T (-1) ω + t)) := by
    apply Measurable.mul
    · exact (measurable_const.indicator hA).comp measurable_fst
    · exact (measurable_const.indicator measurableSet_Ioc).comp
        (((S.N.measurable_T (-1)).comp measurable_fst).add measurable_snd)
  have h1 := mecke_core S _ hv1
  have e1 : ∀ ω, ∫⁻ t, A.indicator (fun _ => (1:ℝ≥0∞)) ω *
      (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (S.N.T (-1) ω + t) ∂(volume : Measure ℝ)
      = A.indicator (fun _ => (1:ℝ≥0∞)) ω := by
    intro ω
    have hm : Measurable fun t : ℝ =>
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (S.N.T (-1) ω + t) :=
      (measurable_const.indicator measurableSet_Ioc).comp (measurable_id.const_add _)
    rw [lintegral_const_mul _ hm, inner_shift_indicator, mul_one]
  simp_rw [e1] at h1
  rw [lintegral_indicator_const hA, one_mul] at h1
  -- second Mecke
  have hv2 : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ (S.N.T 1 ω) ω) *
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t) := by
    apply Measurable.mul
    · exact ((measurable_const.indicator hA).comp hshift).comp measurable_fst
    · exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  have h2 := mecke_core S _ hv2
  have e2 : ∀ ω, ∫⁻ t, A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ (S.N.T 1 ω) ω) *
      (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t ∂(volume : Measure ℝ)
      = A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ (S.N.T 1 ω) ω) := by
    intro ω
    rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Ioc),
      lintegral_indicator_const measurableSet_Ioc]
    simp
  simp_rw [e2] at h2
  have e3 : ∫⁻ ω, A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ (S.N.T 1 ω) ω) ∂S.P0
      = S.P0 ((fun ω => S.θ (S.N.T 1 ω) ω) ⁻¹' A) := by
    rw [← one_mul (S.P0 _), ← lintegral_indicator_const (hshift hA)]
    congr 1
  rw [e3] at h2
  -- the two right-hand sides agree
  have key : ∀ ω, ∫⁻ t, A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ t ω) *
      (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (S.N.T (-1) (S.θ t ω) + t) ∂(S.N.count ω)
      = ∫⁻ t, A.indicator (fun _ => (1:ℝ≥0∞)) (S.θ (S.N.T 1 (S.θ t ω)) (S.θ t ω)) *
      (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t ∂(S.N.count ω) := by
    intro ω
    rw [lintegral_count_shift S _ hv1, lintegral_count_shift S _ hv2]
    simp only [shift_T_at, flow_add]
    have : ∀ n : ℤ, S.N.T (n + 1) ω - S.N.T n ω + S.N.T n ω = S.N.T (n + 1) ω := fun n => by ring
    simp_rw [this]
    have : ∀ n : ℤ, S.N.T (n + -1) ω - S.N.T n ω + S.N.T n ω = S.N.T (n - 1) ω := fun n => by
      ring_nf
    simp_rw [this]
    exact ((Equiv.addRight (1:ℤ)).tsum_eq (fun n => A.indicator (fun _ => (1:ℝ≥0∞))
      (S.θ (S.N.T n ω) ω) * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞))
      (S.N.T (n - 1) ω))).symm.trans (by simp)
  simp_rw [key] at h1
  rw [← h2] at h1
  exact ((ENNReal.mul_right_inj (lam_pos S) ENNReal.ofReal_ne_top).1 h1).symm

/-! ### Neveu's exchange formula -/

lemma indicator_fun_mul {α : Type*} (C : Set α) (g : α → ℝ≥0∞) (x : α) :
    C.indicator g x = g x * C.indicator (fun _ => (1:ℝ≥0∞)) x := by
  classical
  simp only [Set.indicator_apply]; split_ifs <;> simp

lemma measurable_flow_at (θ : Flow Ω) (ω : Ω) : Measurable fun t : ℝ => θ t ω :=
  θ.measurable_uncurry.comp (measurable_id.prodMk measurable_const)

/-- the sum of `f ∘ θ_t` over the points of `N` in `(0, T'_1]` -/
noncomputable def cycleSum (S S' : PalmSetting Ω) (f : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℤ, (Set.Ioc (0:ℝ) (S'.N.T 1 ω)).indicator (fun t => f (S.θ t ω)) (S.N.T n ω)

lemma cycleSum_eq (S S' : PalmSetting Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f) (ω : Ω) :
    ∫⁻ t in Set.Ioc (0 : ℝ) (S'.N.T 1 ω), f (S.θ t ω) ∂(S.N.count ω) = cycleSum S S' f ω := by
  rw [← lintegral_indicator measurableSet_Ioc]
  exact lintegral_count S.N ω _ ((hf.comp (measurable_flow_at S.θ ω)).indicator measurableSet_Ioc)

lemma measurable_cycleSum (S S' : PalmSetting Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    Measurable (cycleSum S S' f) := by
  unfold cycleSum
  apply Measurable.tsum
  intro n
  have : (fun ω => (Set.Ioc (0:ℝ) (S'.N.T 1 ω)).indicator (fun t => f (S.θ t ω)) (S.N.T n ω))
      = {ω | 0 < S.N.T n ω ∧ S.N.T n ω ≤ S'.N.T 1 ω}.indicator
          (fun ω => f (S.θ (S.N.T n ω) ω)) := by
    ext ω
    simp only [Set.indicator_apply, Set.mem_Ioc, Set.mem_setOf_eq]
  rw [this]
  exact (hf.comp (measurable_shiftT S.θ S.N n)).indicator
    ((measurableSet_lt measurable_const (S.N.measurable_T n)).inter
      (measurableSet_le (S.N.measurable_T n) (S'.N.measurable_T 1)))

lemma cycleSum_shift (S S' : PalmSetting Ω) (hflow : S'.θ = S.θ) (f : Ω → ℝ≥0∞) (ω : Ω) (m : ℤ) :
    cycleSum S S' f (S.θ (S'.N.T m ω) ω)
      = ∑' n : ℤ, (Set.Ioc (S'.N.T m ω) (S'.N.T (m + 1) ω)).indicator
          (fun t => f (S.θ t ω)) (S.N.T n ω) := by
  unfold cycleSum
  set s := S'.N.T m ω with hs
  obtain ⟨j, hj⟩ := exists_cycle S.N ω s
  have h1 : S'.N.T 1 (S.θ s ω) = S'.N.T (m + 1) ω - s := by
    have := shift_T_at S' ω m 1
    rw [hflow] at this
    exact this
  have h2 : ∀ n, S.N.T n (S.θ s ω) = S.N.T (j + n) ω - s := shift_T S ω s j hj
  simp_rw [h1, h2]
  have h3 : ∀ n, (Set.Ioc 0 (S'.N.T (m + 1) ω - s)).indicator (fun t => f (S.θ t (S.θ s ω)))
      (S.N.T (j + n) ω - s)
      = (Set.Ioc s (S'.N.T (m + 1) ω)).indicator (fun t => f (S.θ t ω)) (S.N.T (j + n) ω) := by
    intro n
    simp only [Set.indicator_apply, Set.mem_Ioc, flow_add, sub_add_cancel]
    congr 1
    apply propext
    constructor
    · rintro ⟨a, b⟩; constructor <;> linarith
    · rintro ⟨a, b⟩; constructor <;> linarith
  simp_rw [h3]
  exact (Equiv.addLeft j).tsum_eq (fun n => (Set.Ioc s (S'.N.T (m + 1) ω)).indicator
    (fun t => f (S.θ t ω)) (S.N.T n ω))

lemma tsum_swap_aux (a : ℤ → ℝ≥0∞) (b : ℤ → ℤ → ℝ≥0∞) (c : ℤ → ℝ≥0∞) :
    ∑' m, (∑' n, a n * b m n) * c m = ∑' n, a n * ∑' m, c m * b m n := by
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; ext n
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext m
  ring

/-- the last point of `N'` strictly before the origin -/
noncomputable def lastBefore (S' : PalmSetting Ω) (ω : Ω) : ℝ :=
  if S'.N.T 0 ω < 0 then S'.N.T 0 ω else S'.N.T (-1) ω

lemma measurable_lastBefore (S' : PalmSetting Ω) : Measurable (lastBefore S') :=
  Measurable.ite (measurableSet_lt (S'.N.measurable_T 0) measurable_const)
    (S'.N.measurable_T 0) (S'.N.measurable_T (-1))

lemma lastBefore_shift (S S' : PalmSetting Ω) (hflow : S'.θ = S.θ) (ω : Ω) (u : ℝ) :
    ∃ j : ℤ, S'.N.T j ω < u ∧ u ≤ S'.N.T (j + 1) ω ∧ lastBefore S' (S.θ u ω) + u = S'.N.T j ω := by
  obtain ⟨j, hj⟩ := exists_cycle S'.N ω u
  have hk : ∀ k, S'.N.T k (S.θ u ω) = S'.N.T (j + k) ω - u := by
    have := shift_T S' ω u j hj
    rw [hflow] at this
    exact this
  unfold lastBefore
  by_cases h : S'.N.T 0 (S.θ u ω) < 0
  · rw [hk 0, add_zero] at h
    refine ⟨j, by linarith, hj.2.le, ?_⟩
    rw [if_pos, hk 0, add_zero]; ring
    rw [hk 0, add_zero]; exact h
  · rw [hk 0, add_zero] at h
    have heq : S'.N.T j ω = u := by linarith [hj.1]
    refine ⟨j - 1, ?_, ?_, ?_⟩
    · rw [← heq]; exact S'.N.strictMono ω (by omega)
    · rw [show j - 1 + 1 = j by ring, heq]
    · rw [if_neg, hk (-1), show j + -1 = j - 1 by ring]; ring
      rw [hk 0, add_zero]; exact h

lemma cycle_indicator_sum (S S' : PalmSetting Ω) (hflow : S'.θ = S.θ) (ω : Ω) (u : ℝ) :
    ∑' m : ℤ, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (S'.N.T m ω) *
        (Set.Ioc (S'.N.T m ω) (S'.N.T (m + 1) ω)).indicator (fun _ => (1:ℝ≥0∞)) u
      = (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (lastBefore S' (S.θ u ω) + u) := by
  obtain ⟨j, h1, h2, h3⟩ := lastBefore_shift S S' hflow ω u
  rw [h3, tsum_eq_single j]
  · rw [Set.indicator_of_mem (show u ∈ Set.Ioc (S'.N.T j ω) (S'.N.T (j + 1) ω) from ⟨h1, h2⟩),
      mul_one]
  · intro m hm
    have hu : u ∉ Set.Ioc (S'.N.T m ω) (S'.N.T (m + 1) ω) := by
      simp only [Set.mem_Ioc, not_and, not_le]
      intro hlt
      rcases lt_or_gt_of_ne hm with hmj | hmj
      · have := (S'.N.strictMono ω).monotone (show m + 1 ≤ j by omega)
        linarith
      · have := (S'.N.strictMono ω).monotone (show j + 1 ≤ m by omega)
        linarith
    rw [Set.indicator_of_notMem hu, mul_zero]

theorem neveu_core (S S' : PalmSetting Ω)
    (hflow : S'.θ = S.θ) (hprob : S'.P = S.P)
    (f : Ω → ENNReal) (hf : Measurable f) :
    ENNReal.ofReal S.lam * ∫⁻ ω, f ω ∂S.P0
      = ENNReal.ofReal S'.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S'.N.T 1 ω), f (S.θ t ω) ∂(S.N.count ω) ∂S'.P0 := by
  simp_rw [cycleSum_eq S S' f hf]
  -- Mecke for S'
  have hvA : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      cycleSum S S' f ω * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) s) :=
    ((measurable_cycleSum S S' f hf).comp measurable_fst).mul
      ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)
  have hA := mecke_core S' _ hvA
  have eA : ∀ ω, ∫⁻ s, cycleSum S S' f ω * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) s
      ∂(volume : Measure ℝ) = cycleSum S S' f ω := by
    intro ω
    rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Ioc),
      lintegral_indicator_const measurableSet_Ioc]
    simp
  simp_rw [eA] at hA
  rw [hA, hprob]
  -- Mecke for S
  have hvC : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      f ω * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (lastBefore S' ω + t)) :=
    (hf.comp measurable_fst).mul ((measurable_const.indicator measurableSet_Ioc).comp
      (((measurable_lastBefore S').comp measurable_fst).add measurable_snd))
  have hC := mecke_core S _ hvC
  have eC : ∀ ω, ∫⁻ t, f ω * (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞))
      (lastBefore S' ω + t) ∂(volume : Measure ℝ) = f ω := by
    intro ω
    have hm : Measurable fun t : ℝ =>
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) (lastBefore S' ω + t) :=
      (measurable_const.indicator measurableSet_Ioc).comp (measurable_id.const_add _)
    rw [lintegral_const_mul _ hm, inner_shift_indicator, mul_one]
  simp_rw [eC] at hC
  rw [hC]
  -- compare the two stationary sides
  congr 1; ext ω
  rw [lintegral_count_shift S _ hvC]
  have : S'.N.count ω = S'.N.count ω := rfl
  rw [show (fun t => cycleSum S S' f (S'.θ t ω) * (Set.Ioc (0:ℝ) 1).indicator
      (fun _ => (1:ℝ≥0∞)) t) = fun t => cycleSum S S' f (S.θ t ω) *
      (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t by rw [hflow]]
  rw [lintegral_count S'.N ω _ (show Measurable fun t : ℝ => cycleSum S S' f (S.θ t ω) *
      (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) t from
    ((measurable_cycleSum S S' f hf).comp
    (measurable_flow_at S.θ ω)).mul (measurable_const.indicator measurableSet_Ioc))]
  simp_rw [cycleSum_shift S S' hflow f ω]
  simp_rw [indicator_fun_mul _ (fun t => f (S.θ t ω))]
  rw [tsum_swap_aux]
  congr 1; ext n
  rw [cycle_indicator_sum S S' hflow ω]

end PalmQueueing.Palm

open PalmQueueing.Palm
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (S S' : PalmSetting Ω)
    (hflow : S'.θ = S.θ) (hprob : S'.P = S.P)
    (f : Ω → ENNReal) (hf : Measurable f) :
    ENNReal.ofReal S.lam * ∫⁻ ω, f ω ∂S.P0
      = ENNReal.ofReal S'.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S'.N.T 1 ω), f (S.θ t ω) ∂(S.N.count ω) ∂S'.P0 := by
  exact neveu_core S S' hflow hprob f hf
