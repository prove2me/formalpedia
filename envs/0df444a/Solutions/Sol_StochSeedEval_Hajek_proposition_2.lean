-- Prove2me | solution 1 for StochSeedEval.Hajek.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:59:36.922446+00:00
-- url     : https://prove2.me/submissions/d88bbbea-65f9-4768-a2e5-7ae2a2ef0bb1

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators
import Theorems.Thm_StochSeedEval_Hajek_sample_averages
import Theorems.Thm_StochSeedEval_Hajek_consistency
import Theorems.Thm_StochSeedEval_Hajek_variance_identity
import Theorems.Thm_StochSeedEval_Hajek_joint_clt

open MeasureTheory ProbabilityTheory Filter Topology

set_option linter.unusedSectionVars false

namespace HajekRed
open StochSeedEval.Hajek

variable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

section Conv
variable {Ω' Ω'' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω'']
  {P : Measure Ω'} [IsProbabilityMeasure P] {Q : Measure Ω''} [IsProbabilityMeasure Q]

lemma tendstoInMeasure_of_tendstoInDistribution_const {X : ℕ → Ω' → ℝ} (c : ℝ)
    (h : TendstoInDistribution X atTop (fun _ : Ω'' => c) (fun _ => P) Q) :
    TendstoInMeasure P X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  set E : Set ℝ := {x : ℝ | ε ≤ ‖x - c‖} with hE
  have hEm : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  have hfr : frontier E ⊆ {x : ℝ | ε = ‖x - c‖} :=
    frontier_le_subset_eq continuous_const (by fun_prop)
  have hnull : (Q.map (fun _ => c)) (frontier E) = 0 := by
    rw [Measure.map_const]
    refine measure_mono_null hfr ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_eq_fun measurable_const
      (by fun_prop))]
    simp [hε.ne']
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto h.tendsto
    (E := E) (by show ((Q.map (fun _ => c)) (frontier E)).toNNReal = 0; rw [hnull]; rfl)
  have hlim : (Q.map (fun _ => c)) E = 0 := by
    rw [Measure.map_const, Measure.smul_apply, Measure.dirac_apply' _ hEm]
    simp [hE, hε.not_ge]
  have key' : Tendsto (fun n => ((P.map (X n)) E).toNNReal) atTop
      (𝓝 (((Q.map fun _ => c) E).toNNReal)) := key
  rw [hlim, ENNReal.toNNReal_zero] at key'
  have key2 := (NNReal.continuous_coe.tendsto _).comp key'
  simp only [NNReal.coe_zero] at key2
  refine key2.congr fun n => ?_
  simp only [Function.comp_apply, ENNReal.coe_toNNReal_eq_toReal]
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hEm]
  rfl


lemma mul_tendstoInMeasure_zero {U W : ℕ → Ω' → ℝ} {Z : Ω'' → ℝ}
    (hU : TendstoInDistribution U atTop Z (fun _ => P) Q)
    (hW : TendstoInMeasure P W atTop (fun _ => 0)) (hWm : ∀ n, AEMeasurable (W n) P) :
    TendstoInMeasure P (fun n ω => U n ω * W n ω) atTop (fun _ => 0) := by
  have := hU.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hW hWm
  apply tendstoInMeasure_of_tendstoInDistribution_const (Q := Q) 0
  simpa using this

end Conv

lemma sampleAverage_measurable {Ω' : Type*} [MeasurableSpace Ω'] (S : ℕ → Ω' → Ω)
    (hSm : ∀ i, Measurable (S i)) (g : Ω → ℝ) (N : ℕ) :
    Measurable (sampleAverage S g N) := by
  unfold sampleAverage
  have : ∀ i, Measurable (fun ω => g (S i ω)) := fun i => (measurable_of_countable g).comp (hSm i)
  fun_prop

lemma hajek_measurable {Ω' : Type*} [MeasurableSpace Ω'] (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (N : ℕ) :
    Measurable (hajek pA pB pD y S N) := by
  unfold hajek
  have h1 : ∀ i, Measurable (fun ω => weightA pA pD (S i ω)) :=
    fun i => (measurable_of_countable (weightA pA pD)).comp (hSm i)
  have h2 : ∀ i, Measurable (fun ω => weightB pB pD (S i ω)) :=
    fun i => (measurable_of_countable (weightB pB pD)).comp (hSm i)
  have h3 : ∀ i, Measurable (fun ω => y (S i ω)) :=
    fun i => (measurable_of_countable y).comp (hSm i)
  have h4 := sampleAverage_measurable S hSm (weightA pA pD) N
  have h5 := sampleAverage_measurable S hSm (weightB pB pD) N
  fun_prop

lemma hajek_eq {Ω' : Type*} (pA pB pD : PMF Ω) (y : Ω → ℝ) (S : ℕ → Ω' → Ω) (N : ℕ) (ω : Ω') :
    hajek pA pB pD y S N ω =
      sampleAverage S (fun s => weightA pA pD s * y s) N ω / sampleAverage S (weightA pA pD) N ω -
      sampleAverage S (fun s => weightB pB pD s * y s) N ω / sampleAverage S (weightB pB pD) N ω := by
  simp only [hajek, sampleAverage, sub_mul, Finset.sum_sub_distrib, mul_sub, div_eq_mul_inv,
    Finset.mul_sum, Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring


end HajekRed

open StochSeedEval.Hajek HajekRed

theorem solution
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hA2 : MemLp (weightA pA pD) 2 pD.toMeasure)
    (hB2 : MemLp (weightB pB pD) 2 pD.toMeasure)
    (hAy2 : MemLp (fun s => weightA pA pD s * y s) 2 pD.toMeasure)
    (hBy2 : MemLp (fun s => weightB pB pD s * y s) 2 pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure)
    {Ω'' : Type*} [MeasurableSpace Ω''] (Q : Measure Ω'') [IsProbabilityMeasure Q]
    (Z : Ω'' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0 (asymptoticVariance pA pB pD y).toNNReal) Q) :
    (∀ᵐ ω ∂P, Tendsto (fun N => hajek pA pB pD y S N ω) atTop (𝓝 (contrast pA pB y))) ∧
    TendstoInDistribution
      (fun (N : ℕ) ω => Real.sqrt (N : ℝ) * (hajek pA pB pD y S N ω - contrast pA pB y))
      atTop Z (fun _ => P) Q := by
  have hAy := hAy2.integrable one_le_two
  have hBy := hBy2.integrable one_le_two
  refine ⟨consistency pA pB pD y hpos hAy hBy P S hSm hSi hSlaw, ?_⟩
  obtain ⟨-, hLvar⟩ := variance_identity pA pB pD y hpos hA2 hB2 hAy2 hBy2
  have hall := sample_averages pA pB pD y hpos hAy hBy P S hSm hSi hSlaw
  have J := joint_clt pA pB pD y hpos hA2 hB2 hAy2 hBy2 P S hSm hSi hSlaw
  set μA := meanA pA y with hμA
  set μB := meanB pB y with hμB
  set a : ℕ → Ω' → ℝ := fun N ω => sampleAverage S (weightA pA pD) N ω with ha
  set b : ℕ → Ω' → ℝ := fun N ω => sampleAverage S (weightB pB pD) N ω with hb
  set ay : ℕ → Ω' → ℝ := fun N ω => sampleAverage S (fun s => weightA pA pD s * y s) N ω
    with hay
  set by' : ℕ → Ω' → ℝ := fun N ω => sampleAverage S (fun s => weightB pB pD s * y s) N ω
    with hby
  -- main term: the influence function is the linear statistic with c = (-μA, μB, 1, -1)
  have hlin : linearStatistic pA pB pD y ![-μA, μB, 1, -1] = influence pA pB pD y := by
    funext s
    simp only [linearStatistic, influence, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hX := J ![-μA, μB, 1, -1] Q Z (by rw [hlin, hLvar]; exact hZ)
  -- the two remainder directions
  have hUA := joint_clt pA pB pD y hpos hA2 hB2 hAy2 hBy2 P S hSm hSi hSlaw ![-μA, 0, 1, 0]
    (gaussianReal 0 (variance (linearStatistic pA pB pD y ![-μA, 0, 1, 0]) pD.toMeasure).toNNReal)
    id HasLaw.id
  have hUB := joint_clt pA pB pD y hpos hA2 hB2 hAy2 hBy2 P S hSm hSi hSlaw ![0, -μB, 0, 1]
    (gaussianReal 0 (variance (linearStatistic pA pB pD y ![0, -μB, 0, 1]) pD.toMeasure).toNNReal)
    id HasLaw.id
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hX hUA hUB
  have ham : ∀ N, Measurable (a N) := fun N => sampleAverage_measurable S hSm _ N
  have hbm : ∀ N, Measurable (b N) := fun N => sampleAverage_measurable S hSm _ N
  have haym : ∀ N, Measurable (ay N) := fun N => sampleAverage_measurable S hSm _ N
  have hbym : ∀ N, Measurable (by' N) := fun N => sampleAverage_measurable S hSm _ N
  set WA : ℕ → Ω' → ℝ := fun N ω => 1 / a N ω - 1 with hWA
  set WB : ℕ → Ω' → ℝ := fun N ω => 1 - 1 / b N ω with hWB
  have hWAm : ∀ N, AEMeasurable (WA N) P := fun N => by
    have := ham N; simp only [hWA]; fun_prop
  have hWBm : ∀ N, AEMeasurable (WB N) P := fun N => by
    have := hbm N; simp only [hWB]; fun_prop
  have hWAt : TendstoInMeasure P WA atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun N => (hWAm N).aestronglyMeasurable) (by
      filter_upwards [hall] with ω ⟨h1, _⟩
      have := (tendsto_const_nhds (x := (1 : ℝ))).div h1 one_ne_zero |>.sub_const 1
      convert this using 2 <;> simp [hWA, ha])
  have hWBt : TendstoInMeasure P WB atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun N => (hWBm N).aestronglyMeasurable) (by
      filter_upwards [hall] with ω ⟨_, h2, _⟩
      have := (tendsto_const_nhds (x := (1 : ℝ))).div h2 one_ne_zero |>.const_sub 1
      convert this using 2 <;> simp [hWB, hb])
  have hRA := mul_tendstoInMeasure_zero hUA hWAt hWAm
  have hRB := mul_tendstoInMeasure_zero hUB hWBt hWBm
  have hRAm : ∀ N : ℕ, AEMeasurable (fun ω => Real.sqrt (N : ℝ) *
      (-μA * (a N ω - 1) + 0 * (b N ω - 1) + 1 * (ay N ω - μA) + 0 * (by' N ω - μB)) *
      WA N ω) P := fun N => by
    have := ham N; have := hbm N; have := haym N; have := hbym N
    simp only [hWA]; fun_prop
  have hRBm : ∀ N : ℕ, AEMeasurable (fun ω => Real.sqrt (N : ℝ) *
      (0 * (a N ω - 1) + -μB * (b N ω - 1) + 0 * (ay N ω - μA) + 1 * (by' N ω - μB)) *
      WB N ω) P := fun N => by
    have := ham N; have := hbm N; have := haym N; have := hbym N
    simp only [hWB]; fun_prop
  have h1 := hX.add_of_tendstoInMeasure_const hRA hRAm
  have h2 := h1.add_of_tendstoInMeasure_const hRB hRBm
  simp only [add_zero] at h2
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z h2 ?_ ?_
  · refine tendstoInMeasure_of_tendsto_ae (fun N => ?_) ?_
    · have := hajek_measurable pA pB pD y S hSm N
      have := ham N; have := hbm N; have := haym N; have := hbym N
      have := sampleAverage_measurable S hSm (weightA pA pD) N
      have := sampleAverage_measurable S hSm (weightB pB pD) N
      have := sampleAverage_measurable S hSm (fun s => weightA pA pD s * y s) N
      have := sampleAverage_measurable S hSm (fun s => weightB pB pD s * y s) N
      simp only [Pi.sub_apply, Pi.add_apply, hWA, hWB]
      fun_prop
    · filter_upwards [hall] with ω ⟨h1, h2, _, _⟩
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [h1.eventually_ne one_ne_zero, h2.eventually_ne one_ne_zero] with N hA hB
      simp only [Pi.sub_apply, Pi.add_apply, hWA, hWB, Pi.zero_apply]
      rw [hajek_eq]
      unfold contrast
      simp only [ha, hb, hay, hby, hμA, hμB] at hA hB ⊢
      field_simp
      ring
  · intro N
    exact ((hajek_measurable pA pB pD y S hSm N).sub_const _).const_mul _ |>.aemeasurable
