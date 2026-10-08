-- Prove2me | solution 1 for PalmQueueing.Palm.mecke_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:55:04.626815+00:00
-- url     : https://prove2.me/submissions/09e95068-312a-49d8-850c-9608d4909c0d

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.17): Mecke's formula (p.17)
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

end PalmQueueing.Palm

open PalmQueueing.Palm
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (S : PalmSetting Ω) (v : Ω → ℝ → ENNReal)
    (hv : Measurable (Function.uncurry v)) :
    ENNReal.ofReal S.lam * ∫⁻ ω, ∫⁻ t, v ω t ∂(volume : Measure ℝ) ∂S.P0
      = ∫⁻ ω, ∫⁻ t, v (S.θ t ω) t ∂(S.N.count ω) ∂S.P := by
  exact mecke_core S v hv
