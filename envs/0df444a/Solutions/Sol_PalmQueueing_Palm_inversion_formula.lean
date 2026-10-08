-- Prove2me | solution 1 for PalmQueueing.Palm.inversion_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:59:32.302238+00:00
-- url     : https://prove2.me/submissions/50cd6a9d-ae0d-4207-8996-4a35a879c181

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.25): the inversion formula of Ryll-Nardzewski and Slivnyak (p.20)
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

end PalmQueueing.Palm

open PalmQueueing.Palm
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (S : PalmSetting Ω) (f : Ω → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂S.P
      = ENNReal.ofReal S.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S.N.T 1 ω), f (S.θ t ω) ∂(volume : Measure ℝ) ∂S.P0 := by
  exact inversion_core S f hf
