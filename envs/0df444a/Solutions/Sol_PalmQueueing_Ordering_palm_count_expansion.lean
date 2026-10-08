-- Prove2me | solution 1 for PalmQueueing.Ordering.palm_count_expansion
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T12:06:51.798163+00:00
-- url     : https://prove2.me/submissions/bb60ffe9-ded9-4888-899c-80a2ea0fdb78

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
#print axioms PalmQueueing.Palm.mecke_core
#print axioms PalmQueueing.Palm.inversion_core

set_option autoImplicit false
open MeasureTheory PalmQueueing.Palm
open scoped ENNReal
namespace PalmCountCodex
variable {Ω : Type*} [MeasurableSpace Ω]
lemma count_singleton_index (N : PointProcess Ω) (ω : Ω) (j : ℤ) :
    N.count ω {N.T j ω} = 1 := by
  classical
  rw [count_apply N ω _ (measurableSet_singleton _)]
  have he : ∀ n : ℤ, N.T n ω = N.T j ω ↔ n = j := fun n => (N.strictMono ω).injective.eq_iff
  simp [Set.indicator_apply,he]
lemma zero_at_shifted_point (S : PalmSetting Ω) (ω : Ω) (j : ℤ) :
    S.N.T 0 (S.θ (S.N.T j ω) ω) = 0 := by
  have hc : S.N.count (S.θ (S.N.T j ω) ω) {0} = 1 := by
    rw [S.compatible _ _ _ (measurableSet_singleton _)]
    have hs : (fun s : ℝ => s-S.N.T j ω) ⁻¹' {0} = {S.N.T j ω} := by
      ext s
      simp [sub_eq_zero]
    rw [hs]
    exact count_singleton_index S.N ω j
  apply le_antisymm (S.N.zero_le _)
  by_contra hh
  have ht : S.N.T 0 (S.θ (S.N.T j ω) ω) < 0 := lt_of_not_ge hh
  have hz : S.N.count (S.θ (S.N.T j ω) ω) {0} = 0 := by
    apply (count_eq_zero_iff S.N _ _ (measurableSet_singleton _)).mpr
    intro n
    simp only [Set.mem_singleton_iff]
    rcases le_or_gt n 0 with hn | hn
    · have hle := (S.N.strictMono (S.θ (S.N.T j ω) ω)).monotone hn
      linarith
    · have hle := (S.N.strictMono (S.θ (S.N.T j ω) ω)).monotone (show 1 ≤ n by omega)
      have hp := S.N.lt_one (S.θ (S.N.T j ω) ω)
      linarith
  rw [hz] at hc
  exact zero_ne_one hc
lemma palm_zero_ae (S : PalmSetting Ω) : ∀ᵐ ω ∂S.P0, S.N.T 0 ω = 0 := by
  classical
  let A : Set Ω := {ω | S.N.T 0 ω ≠ 0}
  have hm : MeasurableSet A :=
    (measurableSet_eq_fun (S.N.measurable_T 0) measurable_const).compl
  have hz : campbellMeasure S (A ×ˢ Set.Ioc (0 : ℝ) 1) = 0 := by
    rw [campbellMeasure_prod S hm measurableSet_Ioc]
    apply (lintegral_eq_zero_iff (measurable_palmSum S hm measurableSet_Ioc)).mpr
    apply ae_of_all
    intro ω
    simp [palmSum,A,Set.indicator_apply,zero_at_shifted_point]
  have hh := campbellMeasure_prod_Ioc S hm 0 1 (by norm_num)
  rw [hz] at hh
  have hp : ENNReal.ofReal S.lam ≠ 0 := by
    rw [Ne,ENNReal.ofReal_eq_zero,not_le]
    exact S.intensity.1
  have hh' : ENNReal.ofReal S.lam * S.P0 A = 0 := by simpa using hh.symm
  have hA : S.P0 A = 0 := (mul_eq_zero.mp hh').resolve_left hp
  rw [ae_iff]
  exact hA
end PalmCountCodex
#print axioms PalmCountCodex.count_singleton_index
#print axioms PalmCountCodex.zero_at_shifted_point

#print axioms PalmCountCodex.palm_zero_ae

set_option autoImplicit false
namespace PalmCountEnumeration
lemma int_orderIso_eq_of_zero (e : ℤ ≃o ℤ) (he : e 0 = 0) (n : ℤ) : e n = n := by
  have hs : ∀ z : ℤ, e (z+1) = e z+1 := fun z => by simpa using e.map_succ z
  induction n using Int.induction_on with
  | zero => exact he
  | succ n ih =>
    simpa only [Int.natCast_add,Int.natCast_one,ih] using hs (n : ℤ)
  | pred n ih =>
    have hh := hs (-(n : ℤ)-1)
    have heq : -(n : ℤ)-1+1 = -(n : ℤ) := by ring
    rw [heq,ih] at hh
    push_cast
    omega
lemma enumeration_eq_of_range_zero (a b : ℤ → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (hr : Set.range a = Set.range b) (hzero : a 0 = b 0) : a = b := by
  classical
  have hga : ∀ n : ℤ, ∃ m : ℤ, b m = a n := by
    intro n
    have hn : a n ∈ Set.range b := hr ▸ Set.mem_range_self n
    exact hn
  have hfb : ∀ n : ℤ, ∃ m : ℤ, a m = b n := by
    intro n
    have hn : b n ∈ Set.range a := hr.symm ▸ Set.mem_range_self n
    exact hn
  choose g hg using hga
  choose f hf using hfb
  have hm : StrictMono g := by
    intro i j hij
    apply hb.lt_iff_lt.mp
    rw [hg,hg]
    exact ha hij
  have hi : Function.RightInverse f g := by
    intro n
    apply hb.injective
    rw [hg,hf]
  let e := hm.orderIsoOfRightInverse g f hi
  have he0 : e 0 = 0 := by
    apply hb.injective
    exact (hg 0).trans hzero
  have he : ∀ n : ℤ, g n = n := fun n => int_orderIso_eq_of_zero e he0 n
  funext n
  have hh := hg n
  rw [he n] at hh
  exact hh.symm
end PalmCountEnumeration
#print axioms PalmCountEnumeration.int_orderIso_eq_of_zero
#print axioms PalmCountEnumeration.enumeration_eq_of_range_zero

set_option autoImplicit false
open MeasureTheory PalmQueueing.Palm PalmCountCodex PalmCountEnumeration
namespace PalmCountShift
variable {Ω : Type*} [MeasurableSpace Ω]
lemma point_mem_range_iff (N : PointProcess Ω) (ω : Ω) (t : ℝ) :
    t ∈ Set.range (fun n : ℤ => N.T n ω) ↔ N.count ω {t} ≠ 0 := by
  classical
  rw [Ne,count_eq_zero_iff N ω _ (measurableSet_singleton _)]
  simp [Set.mem_range]
lemma point_index_shift (S : PalmSetting Ω) (ω : Ω) (j n : ℤ) :
    S.N.T n (S.θ (S.N.T j ω) ω) = S.N.T (n+j) ω - S.N.T j ω := by
  let a : ℤ → ℝ := fun m => S.N.T m (S.θ (S.N.T j ω) ω)
  let b : ℤ → ℝ := fun m => S.N.T (m+j) ω - S.N.T j ω
  have ha : StrictMono a := S.N.strictMono _
  have hb : StrictMono b := by
    intro i k hik
    change S.N.T (i+j) ω - S.N.T j ω < S.N.T (k+j) ω - S.N.T j ω
    exact sub_lt_sub_right ((S.N.strictMono ω) (show i+j < k+j by omega)) _
  have hz : a 0 = b 0 := by
    dsimp only [a,b]
    rw [zero_at_shifted_point]
    simp
  have hr : Set.range a = Set.range b := by
    ext t
    change t ∈ Set.range (fun m => S.N.T m (S.θ (S.N.T j ω) ω)) ↔ t ∈ Set.range b
    rw [point_mem_range_iff,S.compatible _ _ _ (measurableSet_singleton _)]
    have hs : (fun s : ℝ => s-S.N.T j ω) ⁻¹' {t} = {t+S.N.T j ω} := by
      ext s
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hs,← point_mem_range_iff]
    constructor
    · rintro ⟨m,hm⟩
      refine ⟨m-j,?_⟩
      dsimp only [b]
      rw [sub_add_cancel]
      change S.N.T m ω = t+S.N.T j ω at hm
      linarith
    · rintro ⟨m,hm⟩
      refine ⟨m+j,?_⟩
      dsimp only [b] at hm
      linarith
  exact congrFun (enumeration_eq_of_range_zero a b ha hb hr hz) n
lemma window_lower_index (N : PointProcess Ω) (ω : Ω) (n : ℤ) :
    0 ≤ N.T n ω ↔ (if N.T 0 ω = 0 then (0 : ℤ) else 1) ≤ n := by
  by_cases h0 : N.T 0 ω = 0
  · rw [if_pos h0]
    constructor
    · intro hn
      by_contra h
      have hh := (N.strictMono ω) (lt_of_not_ge h)
      change N.T n ω < N.T 0 ω at hh
      rw [h0] at hh
      linarith
    · intro hn
      have hh := (N.strictMono ω).monotone hn
      change N.T 0 ω ≤ N.T n ω at hh
      rw [h0] at hh
      exact hh
  · rw [if_neg h0]
    have ht : N.T 0 ω < 0 := lt_of_le_of_ne (N.zero_le ω) h0
    constructor
    · intro hn
      by_contra h
      have hh := (N.strictMono ω).monotone (show n ≤ 0 by omega)
      linarith
    · intro hn
      exact (N.lt_one ω).le.trans ((N.strictMono ω).monotone hn)
end PalmCountShift
#print axioms PalmCountShift.point_mem_range_iff
#print axioms PalmCountShift.point_index_shift

#print axioms PalmCountShift.window_lower_index

set_option autoImplicit false
open MeasureTheory Filter PalmQueueing.Palm
open scoped ENNReal
namespace PalmCountWindow
variable {Ω : Type*} [MeasurableSpace Ω]
lemma finite_window_indices (N : PointProcess Ω) (ω : Ω) (a b : ℝ) :
    {n : ℤ | N.T n ω ∈ Set.Ico a b}.Finite := by
  obtain ⟨L,hL⟩ := eventually_atBot.mp ((tendsto_atBot.mp (N.tendsto_atBot ω)) (a-1))
  obtain ⟨U,hU⟩ := eventually_atTop.mp ((tendsto_atTop.mp (N.tendsto_atTop ω)) b)
  apply (Set.finite_Icc L U).subset
  intro n hn
  constructor
  · by_contra h
    have hh := hL n (le_of_lt (lt_of_not_ge h))
    have hx := hn.1
    linarith
  · by_contra h
    have hh := hU n (le_of_lt (lt_of_not_ge h))
    have hx := hn.2
    linarith
noncomputable def windowCard (N : PointProcess Ω) (ω : Ω) (a b : ℝ) : ℕ :=
  (finite_window_indices N ω a b).toFinset.card
lemma window_count_eq_card (N : PointProcess Ω) (ω : Ω) (a b : ℝ) :
    N.count ω (Set.Ico a b) = (windowCard N ω a b : ℝ≥0∞) := by
  classical
  let S := (finite_window_indices N ω a b).toFinset
  rw [count_apply N ω _ measurableSet_Ico]
  have hsum : (∑' n : ℤ, (Set.Ico a b).indicator (fun _ => (1 : ℝ≥0∞)) (N.T n ω)) =
      ∑ n ∈ S, (Set.Ico a b).indicator (fun _ => (1 : ℝ≥0∞)) (N.T n ω) := by
    apply tsum_eq_sum
    intro n hn
    have hx : N.T n ω ∉ Set.Ico a b := by
      intro hx
      exact hn ((finite_window_indices N ω a b).mem_toFinset.mpr hx)
    exact Set.indicator_of_notMem hx _
  rw [hsum]
  have he : ∀ n ∈ S, (Set.Ico a b).indicator (fun _ => (1 : ℝ≥0∞)) (N.T n ω) = 1 := by
    intro n hn
    have hx : N.T n ω ∈ Set.Ico a b := (finite_window_indices N ω a b).mem_toFinset.mp hn
    exact Set.indicator_of_mem hx (fun _ : ℝ => (1 : ℝ≥0∞))
  have hsumone : (∑ n ∈ S, (Set.Ico a b).indicator (fun _ => (1 : ℝ≥0∞)) (N.T n ω)) = ∑ _n ∈ S, (1 : ℝ≥0∞) := Finset.sum_congr rfl he
  rw [hsumone]
  simp [windowCard,S]
lemma window_count_real (N : PointProcess Ω) (ω : Ω) (a b : ℝ) :
    (N.count ω (Set.Ico a b)).toReal = (windowCard N ω a b : ℝ) := by
  rw [window_count_eq_card]
  simp
lemma window_count_ne_top (N : PointProcess Ω) (ω : Ω) (a b : ℝ) :
    N.count ω (Set.Ico a b) ≠ ⊤ := by
  rw [window_count_eq_card]
  simp
lemma window_count_measurable (N : PointProcess Ω) (a b : ℝ) :
    Measurable (fun ω => N.count ω (Set.Ico a b)) := by
  have hm : Measurable (fun ω => ∑' n : ℤ,
      (Set.Ico a b).indicator (fun _ => (1 : ℝ≥0∞)) (N.T n ω)) := by
    apply Measurable.tsum
    intro n
    exact ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).indicator measurableSet_Ico).comp (N.measurable_T n)
  convert hm using 1
  funext ω
  exact count_apply N ω _ measurableSet_Ico
lemma windowCard_measurable (N : PointProcess Ω) (a b : ℝ) :
    Measurable (fun ω => windowCard N ω a b) := by
  have hm := (window_count_measurable N a b).ennreal_toReal.nat_floor
  have he : (fun ω => Nat.floor ((N.count ω (Set.Ico a b)).toReal)) =
      (fun ω => windowCard N ω a b) := by
    funext ω
    rw [window_count_real,Nat.floor_natCast]
  rw [he] at hm
  exact hm
lemma arbitrary_window_payoff_measurable (N : PointProcess Ω) (a b : ℝ) (f : ℝ → ℝ) :
    Measurable (fun ω => f ((N.count ω (Set.Ico a b)).toReal)) := by
  have hm := (measurable_of_countable (fun k : ℕ => f (k : ℝ))).comp (windowCard_measurable N a b)
  simpa only [window_count_real,Function.comp_def] using hm
end PalmCountWindow
#print axioms PalmCountWindow.finite_window_indices
#print axioms PalmCountWindow.window_count_eq_card
#print axioms PalmCountWindow.window_count_real
#print axioms PalmCountWindow.window_count_ne_top
#print axioms PalmCountWindow.window_count_measurable

#print axioms PalmCountWindow.windowCard_measurable

#print axioms PalmCountWindow.arbitrary_window_payoff_measurable

set_option autoImplicit false
open MeasureTheory Filter PalmQueueing.Palm PalmCountShift PalmCountWindow
namespace PalmCountConsecutive
variable {Ω : Type*} [MeasurableSpace Ω]
lemma exists_upper_index (N : PointProcess Ω) (ω : Ω) (x : ℝ) (hx : 0 < x) :
    ∃ U : ℤ, 0 < U ∧ ∀ j : ℤ, N.T j ω < x ↔ j < U := by
  have hb : ∃ b : ℤ, ∀ j : ℤ, x ≤ N.T j ω → b ≤ j := by
    refine ⟨1,?_⟩
    intro j hj
    by_contra h
    have hh := (N.strictMono ω).monotone (show j ≤ 0 by omega)
    have h0 := N.zero_le ω
    linarith
  have he : ∃ j : ℤ, x ≤ N.T j ω := by
    obtain ⟨j,hj⟩ := eventually_atTop.mp ((tendsto_atTop.mp (N.tendsto_atTop ω)) x)
    exact ⟨j,hj j le_rfl⟩
  obtain ⟨U,hU,hmin⟩ := Int.exists_least_of_bdd hb he
  have hpos : 0 < U := by
    obtain ⟨b,hb⟩ := hb
    by_contra h
    have hh := (N.strictMono ω).monotone (le_of_not_gt h)
    have h0 := N.zero_le ω
    linarith
  refine ⟨U,hpos,?_⟩
  intro j
  constructor
  · intro hj
    by_contra h
    have hh := (N.strictMono ω).monotone (le_of_not_gt h)
    linarith
  · intro hj
    by_contra h
    have hh := hmin j (le_of_not_gt h)
    omega
lemma windowCard_interval (N : PointProcess Ω) (ω : Ω) (x : ℝ) (U : ℤ)
    (hU : ∀ j : ℤ, N.T j ω < x ↔ j < U) :
    windowCard N ω 0 x = (U-(if N.T 0 ω = 0 then (0 : ℤ) else 1)).toNat := by
  classical
  unfold windowCard
  have hs : (finite_window_indices N ω 0 x).toFinset =
      Finset.Ico (if N.T 0 ω = 0 then (0 : ℤ) else 1) U := by
    ext j
    simp only [Set.Finite.mem_toFinset,Set.mem_setOf_eq,Set.mem_Ico,Finset.mem_Ico,
      window_lower_index,hU]
  rw [hs,Int.card_Ico]
lemma surviving_pairs_card (N : PointProcess Ω) (ω : Ω) (x : ℝ) (k : ℕ)
    (U : ℤ) (hU : ∀ j : ℤ, N.T j ω < x ↔ j < U) :
    (((finite_window_indices N ω 0 x).toFinset).filter
      (fun j : ℤ => N.T (j+(k : ℤ)) ω < x)).card = windowCard N ω 0 x-k := by
  classical
  let L : ℤ := if N.T 0 ω = 0 then 0 else 1
  have hs : (((finite_window_indices N ω 0 x).toFinset).filter
      (fun j : ℤ => N.T (j+(k : ℤ)) ω < x)) = Finset.Ico L (U-(k : ℤ)) := by
    ext j
    simp only [Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_setOf_eq,Set.mem_Ico,
      Finset.mem_Ico,window_lower_index,hU]
    change (L ≤ j ∧ j < U) ∧ j+(k : ℤ) < U ↔ L ≤ j ∧ j < U-(k : ℤ)
    omega
  rw [hs,Int.card_Ico,windowCard_interval N ω x U hU]
  change (U-(k : ℤ)-L).toNat = (U-L).toNat-k
  omega
end PalmCountConsecutive
#print axioms PalmCountConsecutive.exists_upper_index
#print axioms PalmCountConsecutive.windowCard_interval
#print axioms PalmCountConsecutive.surviving_pairs_card

set_option autoImplicit false
open MeasureTheory PalmQueueing.Palm PalmCountShift PalmCountWindow PalmCountConsecutive
open scoped ENNReal
namespace PalmCountKernel
variable {Ω : Type*} [MeasurableSpace Ω]
def kernelSet (S : PalmSetting Ω) (k : ℕ) (x : ℝ) : Set (Ω × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 < x ∧ S.N.T (k : ℤ) p.1 < x-p.2}
noncomputable def windowTest (S : PalmSetting Ω) (k : ℕ) (x : ℝ) : Ω × ℝ → ℝ≥0∞ :=
  (kernelSet S k x).indicator (fun _ => 1)
lemma kernelSet_measurable (S : PalmSetting Ω) (k : ℕ) (x : ℝ) :
    MeasurableSet (kernelSet S k x) :=
  (measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_lt measurable_snd measurable_const).inter
      (measurableSet_lt ((S.N.measurable_T (k : ℤ)).comp measurable_fst)
        (measurable_const.sub measurable_snd)))
lemma windowTest_measurable (S : PalmSetting Ω) (k : ℕ) (x : ℝ) :
    Measurable (windowTest S k x) :=
  measurable_const.indicator (kernelSet_measurable S k x)
lemma shifted_test_term (S : PalmSetting Ω) (ω : Ω) (k : ℕ) (x : ℝ) (j : ℤ) :
    windowTest S k x (S.θ (S.N.T j ω) ω,S.N.T j ω) =
      if S.N.T j ω ∈ Set.Ico 0 x ∧ S.N.T (j+(k : ℤ)) ω < x then 1 else 0 := by
  classical
  unfold windowTest
  rw [Set.indicator_apply]
  have he : (S.θ (S.N.T j ω) ω,S.N.T j ω) ∈ kernelSet S k x ↔
      S.N.T j ω ∈ Set.Ico 0 x ∧ S.N.T (j+(k : ℤ)) ω < x := by
    simp only [kernelSet,Set.mem_setOf_eq,Set.mem_Ico,point_index_shift]
    constructor
    · rintro ⟨ha,hb,hc⟩
      refine ⟨⟨ha,hb⟩,?_⟩
      rw [add_comm] at hc
      linarith
    · rintro ⟨⟨ha,hb⟩,hc⟩
      refine ⟨ha,hb,?_⟩
      rw [add_comm]
      linarith
  rw [he]
  split_ifs <;> rfl
lemma sum_shifted_tests (S : PalmSetting Ω) (ω : Ω) (k : ℕ) (x : ℝ) (hx : 0 < x) :
    (∑' j : ℤ, windowTest S k x (S.θ (S.N.T j ω) ω,S.N.T j ω)) =
      (windowCard S.N ω 0 x-k : ℕ) := by
  classical
  let A := ((finite_window_indices S.N ω 0 x).toFinset).filter
    (fun j : ℤ => S.N.T (j+(k : ℤ)) ω < x)
  have he : ∀ j : ℤ, windowTest S k x (S.θ (S.N.T j ω) ω,S.N.T j ω) =
      if j ∈ A then (1 : ℝ≥0∞) else 0 := by
    intro j
    rw [shifted_test_term]
    simp only [A,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_setOf_eq]
  simp_rw [he]
  rw [tsum_eq_sum (s := A) (fun j hj => if_neg hj)]
  have hs : (∑ j ∈ A, if j ∈ A then (1 : ℝ≥0∞) else 0) = (A.card : ℝ≥0∞) := by
    simp
  rw [hs]
  obtain ⟨U,hUpos,hU⟩ := exists_upper_index S.N ω x hx
  have hc : A.card = windowCard S.N ω 0 x-k := surviving_pairs_card S.N ω x k U hU
  exact congrArg (fun m : ℕ => (m : ℝ≥0∞)) hc
lemma mecke_count_kernel (S : PalmSetting Ω) (k : ℕ) (x : ℝ) (hx : 0 < x) :
    ENNReal.ofReal S.lam * ∫⁻ ω, ∫⁻ t, windowTest S k x (ω,t) ∂(volume : Measure ℝ) ∂S.P0 =
      ∫⁻ ω, (windowCard S.N ω 0 x-k : ℕ) ∂S.P := by
  have hm : Measurable (Function.uncurry (fun ω t => windowTest S k x (ω,t))) :=
    windowTest_measurable S k x
  have hh := mecke_core S (fun ω t => windowTest S k x (ω,t)) hm
  rw [hh]
  apply lintegral_congr
  intro ω
  rw [lintegral_count_shift S _ hm]
  exact sum_shifted_tests S ω k x hx
end PalmCountKernel
#print axioms PalmCountKernel.kernelSet_measurable
#print axioms PalmCountKernel.windowTest_measurable
#print axioms PalmCountKernel.shifted_test_term
#print axioms PalmCountKernel.sum_shifted_tests
#print axioms PalmCountKernel.mecke_count_kernel

set_option autoImplicit false
open MeasureTheory PalmQueueing.Palm PalmCountCodex PalmCountWindow PalmCountKernel
open scoped ENNReal
namespace PalmCountStopLoss
variable {Ω : Type*} [MeasurableSpace Ω]
lemma palm_natural_point_nonneg (S : PalmSetting Ω) (k : ℕ) :
    ∀ᵐ ω ∂S.P0, 0 ≤ S.N.T (k : ℤ) ω := by
  filter_upwards [palm_zero_ae S] with ω hω
  have hh := (S.N.strictMono ω).monotone (Int.natCast_nonneg k)
  change S.N.T 0 ω ≤ S.N.T (k : ℤ) ω at hh
  rwa [hω] at hh
lemma inner_window_volume (S : PalmSetting Ω) (ω : Ω) (k : ℕ) (x : ℝ)
    (hn : 0 ≤ S.N.T (k : ℤ) ω) :
    (∫⁻ t, windowTest S k x (ω,t) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal (max (x-S.N.T (k : ℤ) ω) 0) := by
  classical
  have he : (fun t => windowTest S k x (ω,t)) =
      (Set.Ico 0 (x-S.N.T (k : ℤ) ω)).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext t
    unfold windowTest
    rw [Set.indicator_apply,Set.indicator_apply]
    have hh : (ω,t) ∈ kernelSet S k x ↔ t ∈ Set.Ico 0 (x-S.N.T (k : ℤ) ω) := by
      simp only [kernelSet,Set.mem_setOf_eq,Set.mem_Ico]
      constructor
      · rintro ⟨ha,hb,hc⟩
        exact ⟨ha,by linarith⟩
      · rintro ⟨ha,hb⟩
        exact ⟨ha,by linarith,by linarith⟩
    rw [hh]
    split_ifs <;> rfl
  rw [he,lintegral_indicator_const measurableSet_Ico]
  simp
lemma palm_stop_loss_ennreal (S : PalmSetting Ω) (k : ℕ) (x : ℝ) (hx : 0 < x) :
    (∫⁻ ω, (windowCard S.N ω 0 x-k : ℕ) ∂S.P) =
      ENNReal.ofReal S.lam * ∫⁻ ω, ENNReal.ofReal (max (x-S.N.T (k : ℤ) ω) 0) ∂S.P0 := by
  rw [← mecke_count_kernel S k x hx]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [palm_natural_point_nonneg S k] with ω hω
  exact inner_window_volume S ω k x hω
end PalmCountStopLoss
#print axioms PalmCountStopLoss.palm_natural_point_nonneg
#print axioms PalmCountStopLoss.inner_window_volume
#print axioms PalmCountStopLoss.palm_stop_loss_ennreal

set_option autoImplicit false
open MeasureTheory PalmQueueing.Palm PalmCountWindow PalmCountStopLoss
open scoped ENNReal
namespace PalmCountReal
variable {Ω : Type*} [MeasurableSpace Ω]
lemma nat_difference_cast (m k : ℕ) :
    max ((m : ℝ)-(k : ℝ)) 0 = ((m-k : ℕ) : ℝ) := by
  by_cases hk : k ≤ m
  · rw [Nat.cast_sub hk,max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr hk))]
  · have hm : m ≤ k := le_of_not_ge hk
    rw [Nat.sub_eq_zero_of_le hm,max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr hm))]
    simp
lemma residual_integrable (S : PalmSetting Ω) (k : ℕ) (x : ℝ) (hx : 0 < x) :
    Integrable (fun ω => max (x-S.N.T (k : ℤ) ω) 0) S.P0 := by
  letI := S.palm.1
  apply Integrable.of_bound
    ((measurable_const.sub (S.N.measurable_T (k : ℤ))).max measurable_const).aestronglyMeasurable x
  filter_upwards [palm_natural_point_nonneg S k] with ω hω
  change ‖max (x-S.N.T (k : ℤ) ω) 0‖ ≤ x
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) hx.le
lemma count_stop_loss_integrable (S : PalmSetting Ω) (k : ℕ) (x : ℝ) (hx : 0 < x) :
    Integrable (fun ω => ((windowCard S.N ω 0 x-k : ℕ) : ℝ)) S.P := by
  have hm : Measurable (fun ω => ((windowCard S.N ω 0 x-k : ℕ) : ℝ≥0∞)) := by
    simpa only [Function.comp_def] using
      (measurable_of_countable (fun m : ℕ => ((m-k : ℕ) : ℝ≥0∞))).comp
        (windowCard_measurable S.N 0 x)
  have hrm : AEStronglyMeasurable (fun ω => max (x-S.N.T (k : ℤ) ω) 0) S.P0 :=
    (residual_integrable S k x hx).aestronglyMeasurable
  have hf : (∫⁻ ω, ((windowCard S.N ω 0 x-k : ℕ) : ℝ≥0∞) ∂S.P) ≠ ⊤ := by
    rw [palm_stop_loss_ennreal S k x hx]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((lintegral_ofReal_ne_top_iff_integrable hrm
        (ae_of_all _ (fun _ => le_max_right _ _))).mpr (residual_integrable S k x hx))
  simpa only [ENNReal.toReal_natCast] using integrable_toReal_of_lintegral_ne_top hm.aemeasurable hf
lemma palm_stop_loss_real (S : PalmSetting Ω) (k : ℕ) (x : ℝ) (hx : 0 < x) :
    (∫ ω, max ((S.N.count ω (Set.Ico (0 : ℝ) x)).toReal-(k : ℝ)) 0 ∂S.P) =
      S.lam * ∫ ω, max (x-S.N.T (k : ℤ) ω) 0 ∂S.P0 := by
  have hi := count_stop_loss_integrable S k x hx
  have hr := residual_integrable S k x hx
  have hh := palm_stop_loss_ennreal S k x hx
  have he : ∀ ω, ENNReal.ofReal (((windowCard S.N ω 0 x-k : ℕ) : ℝ)) =
      ((windowCard S.N ω 0 x-k : ℕ) : ℝ≥0∞) := fun _ => by simp
  have hn : 0 ≤ᵐ[S.P] (fun ω => ((windowCard S.N ω 0 x-k : ℕ) : ℝ)) :=
    ae_of_all _ (fun _ => Nat.cast_nonneg _)
  have hnr : 0 ≤ᵐ[S.P0] (fun ω => max (x-S.N.T (k : ℤ) ω) 0) :=
    ae_of_all _ (fun _ => le_max_right _ _)
  have hleft := integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable
  simp_rw [he] at hleft
  rw [hh,ENNReal.toReal_mul,ENNReal.toReal_ofReal S.intensity.1.le,
    ← integral_eq_lintegral_of_nonneg_ae hnr hr.aestronglyMeasurable] at hleft
  simpa only [window_count_real,nat_difference_cast] using hleft
end PalmCountReal
#print axioms PalmCountReal.nat_difference_cast
#print axioms PalmCountReal.residual_integrable
#print axioms PalmCountReal.count_stop_loss_integrable
#print axioms PalmCountReal.palm_stop_loss_real

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace PalmCountExpansion
noncomputable def secondDifference (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f (n+1) - 2*f n + f (n-1)
lemma sum_secondDifference (f : ℕ → ℝ) (k : ℕ) :
    (∑ n ∈ range (k+1), secondDifference f n) = f (k+1)-f k := by
  induction k with
  | zero => simp [secondDifference]; ring
  | succ k ih =>
    rw [sum_range_succ,ih]
    simp only [secondDifference,Nat.add_sub_cancel]
    ring
lemma weighted_secondDifference (f : ℕ → ℝ) (hf : f 0 = 0) (k : ℕ) :
    (∑ n ∈ range k, secondDifference f n * ((k-n : ℕ) : ℝ)) = f k := by
  induction k with
  | zero => simp [hf]
  | succ k ih =>
    rw [sum_range_succ]
    have he : ∀ n ∈ range k, ((k+1-n : ℕ) : ℝ) = ((k-n : ℕ) : ℝ)+1 := by
      intro n hn
      have hnk : n ≤ k := (mem_range.mp hn).le
      have hh : k+1-n = (k-n)+1 := by omega
      rw [hh]
      push_cast
      rfl
    have hs : (∑ n ∈ range k, secondDifference f n * ((k+1-n : ℕ) : ℝ)) =
        (∑ n ∈ range k, secondDifference f n * ((k-n : ℕ) : ℝ)) +
        ∑ n ∈ range k, secondDifference f n := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro n hn
      rw [he n hn]
      ring
    rw [hs,ih]
    have hsum := sum_secondDifference f k
    rw [sum_range_succ] at hsum
    norm_num [Nat.succ_eq_add_one,Nat.add_sub_cancel_left] at *
    linarith
lemma real_predecessor_cast (n : ℕ) : max ((n : ℝ)-1) 0 = ((n-1 : ℕ) : ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [add_sub_cancel_right,max_eq_left hn]
lemma original_coefficient (f : ℝ → ℝ) (n : ℕ) :
    secondDifference (fun k : ℕ => f (k : ℝ)) n =
      f ((n : ℝ)+1)-2*f (n : ℝ)+f (max ((n : ℝ)-1) 0) := by
  unfold secondDifference
  rw [real_predecessor_cast]
  simp
lemma original_series_pointwise (f : ℝ → ℝ) (hf : f 0 = 0) (k : ℕ) :
    f (k : ℝ) = ∑' n : ℕ,
      (f ((n : ℝ)+1)-2*f (n : ℝ)+f (max ((n : ℝ)-1) 0)) * max ((k : ℝ)-(n : ℝ)) 0 := by
  have hz : ∀ n ∉ range k,
      (f ((n : ℝ)+1)-2*f (n : ℝ)+f (max ((n : ℝ)-1) 0)) * max ((k : ℝ)-(n : ℝ)) 0 = 0 := by
    intro n hn
    have hkn : k ≤ n := le_of_not_gt (fun h => hn (mem_range.mpr h))
    rw [max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr hkn)),mul_zero]
  rw [tsum_eq_sum hz]
  have hh := weighted_secondDifference (fun m : ℕ => f (m : ℝ)) (by simpa using hf) k
  rw [← hh]
  apply sum_congr rfl
  intro n hn
  rw [original_coefficient]
  have hnk : n ≤ k := (mem_range.mp hn).le
  rw [Nat.cast_sub hnk,max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr hnk))]
end PalmCountExpansion
#print axioms PalmCountExpansion.sum_secondDifference
#print axioms PalmCountExpansion.weighted_secondDifference
#print axioms PalmCountExpansion.real_predecessor_cast
#print axioms PalmCountExpansion.original_coefficient

#print axioms PalmCountExpansion.original_series_pointwise

set_option autoImplicit false
open MeasureTheory PalmQueueing.Palm PalmCountWindow PalmCountExpansion
namespace PalmCountPointwise
variable {Ω : Type*} [MeasurableSpace Ω]
lemma original_window_series (N : PointProcess Ω) (ω : Ω) (f : ℝ → ℝ)
    (hf : f 0 = 0) (x : ℝ) :
    f ((N.count ω (Set.Ico (0 : ℝ) x)).toReal) = ∑' n : ℕ,
      (f ((n : ℝ)+1)-2*f (n : ℝ)+f (max ((n : ℝ)-1) 0)) *
        max ((N.count ω (Set.Ico (0 : ℝ) x)).toReal-(n : ℝ)) 0 := by
  simp_rw [window_count_real]
  exact original_series_pointwise f hf (windowCard N ω 0 x)
end PalmCountPointwise
#print axioms PalmCountPointwise.original_window_series

set_option autoImplicit false
open MeasureTheory PalmQueueing.Palm PalmCountWindow PalmCountReal PalmCountPointwise
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (S : PalmSetting Ω) (f : ℝ → ℝ) (hf0 : f 0 = 0) (x : ℝ) (hx : 0 < x)
    (hsum : Summable fun n : ℕ =>
      |f ((n : ℝ) + 1) - 2 * f (n : ℝ) + f (max ((n : ℝ) - 1) 0)| *
        (S.lam * ∫ ω, max (x - S.N.T (n : ℤ) ω) 0 ∂S.P0)) :
    ∫ ω, f ((S.N.count ω (Set.Ico (0 : ℝ) x)).toReal) ∂S.P
      = ∑' n : ℕ,
          (f ((n : ℝ) + 1) - 2 * f (n : ℝ) + f (max ((n : ℝ) - 1) 0)) *
            (S.lam * ∫ ω, max (x - S.N.T (n : ℤ) ω) 0 ∂S.P0) := by
  let c : ℕ → ℝ := fun n => f ((n : ℝ)+1)-2*f (n : ℝ)+f (max ((n : ℝ)-1) 0)
  let K : ℕ → Ω → ℝ := fun n ω => max ((S.N.count ω (Set.Ico (0 : ℝ) x)).toReal-(n : ℝ)) 0
  let F : ℕ → Ω → ℝ := fun n ω => c n*K n ω
  have hiK : ∀ n, Integrable (K n) S.P := by
    intro n
    simpa only [K,window_count_real,nat_difference_cast] using count_stop_loss_integrable S n x hx
  have hiF : ∀ n, Integrable (F n) S.P := fun n => (hiK n).const_mul (c n)
  have hnorm : ∀ n, (∫ ω, ‖F n ω‖ ∂S.P) =
      |c n| *(S.lam*∫ ω, max (x-S.N.T (n : ℤ) ω) 0 ∂S.P0) := by
    intro n
    have he : (fun ω => ‖F n ω‖) = (fun ω => |c n| *K n ω) := by
      funext ω
      simp only [F,Real.norm_eq_abs,abs_mul]
      rw [abs_of_nonneg (show 0 ≤ K n ω from le_max_right _ _)]
    have hK : (∫ ω, K n ω ∂S.P) = S.lam*∫ ω, max (x-S.N.T (n : ℤ) ω) 0 ∂S.P0 :=
      palm_stop_loss_real S n x hx
    rw [he,integral_const_mul,hK]
  have hs : Summable (fun n => ∫ ω, ‖F n ω‖ ∂S.P) := by
    simp_rw [hnorm]
    exact hsum
  have hh := hasSum_integral_of_summable_integral_norm hiF hs
  have hpoint : ∀ ω, (∑' n, F n ω) = f ((S.N.count ω (Set.Ico (0 : ℝ) x)).toReal) := by
    intro ω
    exact (original_window_series S.N ω f hf0 x).symm
  have he : (fun ω => ∑' n, F n ω) =
      (fun ω => f ((S.N.count ω (Set.Ico (0 : ℝ) x)).toReal)) := funext hpoint
  rw [he] at hh
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro n
  change (∫ ω, c n*K n ω ∂S.P) = c n*(S.lam*∫ ω, max (x-S.N.T (n : ℤ) ω) 0 ∂S.P0)
  rw [integral_const_mul]
  have hK : (∫ ω, K n ω ∂S.P) = S.lam*∫ ω, max (x-S.N.T (n : ℤ) ω) 0 ∂S.P0 :=
    palm_stop_loss_real S n x hx
  rw [hK]

#print axioms solution

/-!
# Lemma 4.4.1: the Palm expansion of a functional of the count (§4.4, p.295)
-/

namespace PalmQueueing.Ordering

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 4.4.1** (p.295). Let `N` be a stationary point process with finite intensity. For all
functions `f : ℝ₊ → ℝ` with `f(0) = 0`, and for all `x > 0`,

`(4.4.1)  E_P[f(N[0,x))] = Σ_{n=0}^{∞} ( f(n+1) − 2f(n) + f((n−1)⁺) ) λ E_{P⁰}(x − T_n)⁺`.

A stationary expectation of a functional of the count in a window is expanded into a series of
**second differences** of `f` against Palm expectations of the residual window `(x − T_n)⁺`. The
second difference is what makes the lemma useful: `f` convex means every coefficient
`f(n+1) − 2f(n) + f((n−1)⁺)` is non-negative, so the whole expansion is monotone in the quantities
`E_{P⁰}(x − T_n)⁺` — which is exactly what Property 4.4.1 needs to turn a `≤_cx` comparison of the
`T_n[P⁰]` into a `≤_cx` comparison of the counts `N[0,x)[P]`.

That equivalence, Property 4.4.1, is the point of §4.4:

> (i) `T_n[P⁰] ≤_cx T̃_n[P̃⁰]` for all `n ≥ 1`;  (ii) `N[0,x)[P] ≤_cx Ñ[0,x)[P̃]` for all
> `x ∈ ℝ₊`

are equivalent. The section's Example 4.4.1, "Feller's paradox revisited", shows that the
corresponding statement for `≤_i` is **false** — the Palm order does not pass to the stationary
one — so the restriction to `≤_cx` is essential and this lemma is where it enters.

`f(0) = 0` is a hypothesis, not a normalisation: the coefficient at `n = 0` is
`f(1) − 2f(0) + f(0) = f(1) − f(0)`, and the series is arranged around it.

**Correction of the page (recorded in `HARD.md`).** The page states (4.4.1) "for all functions
`f`" without saying in what sense the series converges, and read literally it is false: the
second differences telescope, `Σ_{n ≤ M} Δ²f(n) a_n = Σ_{k ≤ M} f(k) P(N[0,x) = k)
+ f(M+1) a_M − f(M) a_{M+1}` with `a_n = λE_{P⁰}(x − T_n)⁺ = E_P(N[0,x) − n)⁺`, and for a mixed
Poisson `N` with heavy-tailed intensity and `f` supported on a sparse set the boundary term does
not vanish although `E_P|f(N[0,x))| < ∞`. The theorem is therefore stated under the hypothesis
that the series of (4.4.1) converges absolutely, `Σ_n |Δ²f(n)| λE_{P⁰}(x − T_n)⁺ < ∞`, which
covers the use the book makes of it (convex `f`, where every term is non-negative) and makes the
right-hand side an honest sum rather than Lean's `tsum` of a non-summable family (`= 0`). -/
example (S : PalmSetting Ω) (f : ℝ → ℝ) (hf0 : f 0 = 0) (x : ℝ) (hx : 0 < x)
    (hsum : Summable fun n : ℕ =>
      |f ((n : ℝ) + 1) - 2 * f (n : ℝ) + f (max ((n : ℝ) - 1) 0)| *
        (S.lam * ∫ ω, max (x - S.N.T (n : ℤ) ω) 0 ∂S.P0)) :
    ∫ ω, f ((S.N.count ω (Set.Ico (0 : ℝ) x)).toReal) ∂S.P
      = ∑' n : ℕ,
          (f ((n : ℝ) + 1) - 2 * f (n : ℝ) + f (max ((n : ℝ) - 1) 0)) *
            (S.lam * ∫ ω, max (x - S.N.T (n : ℤ) ω) 0 ∂S.P0) := by
  exact solution S f hf0 x hx hsum

end PalmQueueing.Ordering

#print axioms solution
