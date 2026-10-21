-- Prove2me | solution 1 for TailRiskSharing.TailConv.embrechts_cor1_varL_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:42:19.26345+00:00
-- url     : https://prove2.me/submissions/1d398d43-fbff-41e3-8377-ecdc7352c8ea

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

set_option autoImplicit false
open MeasureTheory TailRiskSharing.TailConv TailRiskSharing.VaRConv

theorem trt_distFn_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) (y : ℝ) (hy : y < -C) : distFn P X y = 0 := by
  unfold distFn
  have hnull : P {ω | X ω ≤ y} = 0 := by
    refine measure_mono_null (t := {ω | ¬ |X ω| ≤ C}) ?_ (ae_iff.mp hC)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro habs
    have := (abs_le.mp habs).1
    linarith
  simp [Measure.real, hnull]

theorem trt_distFn_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) (y : ℝ) (hy : C ≤ y) :
    distFn P X y = 1 := by
  unfold distFn
  have hs : MeasurableSet {ω | X ω ≤ y} := measurableSet_le hX measurable_const
  have h0 : P {ω | X ω ≤ y}ᶜ = 0 := by
    refine measure_mono_null (t := {ω | ¬ |X ω| ≤ C}) ?_ (ae_iff.mp hC)
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hω ⊢
    intro habs
    exact hω (le_trans (abs_le.mp habs).2 hy)
  have := (prob_compl_eq_zero_iff hs).mp h0
  simp [Measure.real, this]

theorem trt_distFn_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) {y z : ℝ} (h : y ≤ z) : distFn P X y ≤ distFn P X z := by
  unfold distFn
  exact measureReal_mono (fun ω hω => le_trans hω h) (measure_ne_top _ _)

theorem trt_member {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : X ∈ Linf P) (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1) (δ : ℝ) (hδ : 0 < δ) :
    1 - a ≤ distFn P X (VaRL P a X + δ) := by
  obtain ⟨hm, C, hC⟩ := hX
  have hne : {y : ℝ | 1 - a ≤ distFn P X y}.Nonempty := by
    refine ⟨C, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [trt_distFn_one P X hm C hC C le_rfl]
    linarith
  have hlt : VaRL P a X < VaRL P a X + δ := by linarith
  unfold VaRL at hlt ⊢
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne hlt
  exact le_trans hs (trt_distFn_mono P X hslt.le)

theorem trt_upper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : X ∈ Linf P) (a : ℝ) (ha : a < 1) (c : ℝ) (hc : 1 - a ≤ distFn P X c) :
    VaRL P a X ≤ c := by
  obtain ⟨hm, C, hC⟩ := hX
  have hbdd : BddBelow {y : ℝ | 1 - a ≤ distFn P X y} := by
    refine ⟨-C, fun y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    have h0 := trt_distFn_zero P X C hC y hlt
    have hy' : 1 - a ≤ distFn P X y := hy
    rw [h0] at hy'
    linarith
  exact csInf_le hbdd hc

theorem trt_sum_mem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Xs : Fin n → Ω → ℝ) (hXs : ∀ i, Xs i ∈ Linf P) :
    (fun ω => ∑ i, Xs i ω) ∈ Linf P := by
  have hm : ∀ i, Measurable (Xs i) := fun i => (hXs i).1
  choose C hC using fun i => (hXs i).2
  refine ⟨?_, ∑ i, C i, ?_⟩
  · exact Finset.measurable_sum _ (fun i _ => hm i)
  · have : ∀ᵐ ω ∂P, ∀ i, |Xs i ω| ≤ C i := ae_all_iff.mpr hC
    filter_upwards [this] with ω h
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n) (εs : Fin n → ℝ)
    (hε : ∀ i, 0 < εs i ∧ εs i < 1) (hsum : ∑ i, εs i < 1) (Xs : Fin n → Ω → ℝ)
    (hXs : ∀ i, Xs i ∈ Linf P) :
    TailRiskSharing.VaRConv.VaRL P (∑ i, εs i) (fun ω => ∑ i, Xs i ω) ≤ ∑ i, TailRiskSharing.VaRConv.VaRL P (εs i) (Xs i) := by
  have hm : ∀ i, Measurable (Xs i) := fun i => (hXs i).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_of_forall_pos_le_add fun η hη => ?_
  set δ : ℝ := η / n with hδ
  have hδpos : 0 < δ := by positivity
  set y : Fin n → ℝ := fun i => VaRL P (εs i) (Xs i) + δ with hy
  set c : ℝ := ∑ i, y i with hc
  have hcsum : c = ∑ i, VaRL P (εs i) (Xs i) + η := by
    simp only [hc, hy, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hδ]; field_simp
  rw [← hcsum]
  refine trt_upper P _ (trt_sum_mem P n Xs hXs) _ hsum c ?_
  set B : Fin n → Set Ω := fun i => {ω | ¬ Xs i ω ≤ y i} with hB
  have hBm : ∀ i, MeasurableSet (B i) := fun i => (measurableSet_le (hm i) measurable_const).compl
  have hBr : ∀ i, P.real (B i) ≤ εs i := by
    intro i
    have h1 := trt_member P (Xs i) (hXs i) (εs i) (hε i).1.le (hε i).2 δ hδpos
    have h2 : P.real (B i) = 1 - distFn P (Xs i) (y i) := by
      have : B i = {ω | Xs i ω ≤ y i}ᶜ := rfl
      rw [this, measureReal_compl (measurableSet_le (hm i) measurable_const)]
      simp [distFn]
    rw [h2]; linarith
  have hsub : {ω | ∑ i, Xs i ω ≤ c}ᶜ ⊆ ⋃ i, B i := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists, hB, Set.mem_setOf_eq, not_not] at hnot
    exact hω (Finset.sum_le_sum fun i _ => hnot i)
  have hunion : P.real (⋃ i, B i) ≤ ∑ i, P.real (B i) := by
    unfold Measure.real
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _))
      (measure_iUnion_fintype_le _ _)
  have hmeasS : MeasurableSet {ω | ∑ i, Xs i ω ≤ c} :=
    measurableSet_le (Finset.measurable_sum _ (fun i _ => hm i)) measurable_const
  have h3 : P.real {ω | ∑ i, Xs i ω ≤ c}ᶜ ≤ ∑ i, εs i :=
    calc P.real {ω | ∑ i, Xs i ω ≤ c}ᶜ ≤ P.real (⋃ i, B i) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ i, P.real (B i) := hunion
      _ ≤ ∑ i, εs i := Finset.sum_le_sum fun i _ => hBr i
  rw [measureReal_compl hmeasS] at h3
  have : distFn P (fun ω => ∑ i, Xs i ω) c = P.real {ω | ∑ i, Xs i ω ≤ c} := rfl
  rw [this]
  simp at h3
  linarith
