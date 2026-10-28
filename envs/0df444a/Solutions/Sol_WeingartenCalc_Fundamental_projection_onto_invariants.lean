-- Prove2me | solution 1 for WeingartenCalc.Fundamental.projection_onto_invariants
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:30:32.071517+00:00
-- url     : https://prove2.me/submissions/833eee49-ca71-4a0d-9973-2b3fa1394e31

import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem tensorPow_mul' {G : Type*} [Group G] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (d : ℕ) (g h : G) : tensorPow U d (g * h) = tensorPow U d g * tensorPow U d h := by
  ext i j
  have : (U (g * h) : Matrix (Fin N) (Fin N) ℂ) = (U g : Matrix (Fin N) (Fin N) ℂ) * (U h : Matrix (Fin N) (Fin N) ℂ) := by
    rw [map_mul]; rfl
  simp only [tensorPow, Matrix.of_apply, this, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [Finset.prod_mul_distrib]

theorem tensorPow_inv_apply {G : Type*} [Group G] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (d : ℕ) (g : G) (i j : Fin d → Fin N) :
    (starRingEnd ℂ) (tensorPow U d g j i) = tensorPow U d g⁻¹ i j := by
  simp only [tensorPow, Matrix.of_apply, map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  have : (U g⁻¹ : Matrix (Fin N) (Fin N) ℂ) = star (U g : Matrix (Fin N) (Fin N) ℂ) := by
    rw [map_inv]; rfl
  rw [this]
  rfl

theorem tensorPow_cont {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (hU : Continuous U) (d : ℕ) (i j : Fin d → Fin N) :
    Continuous fun g => tensorPow U d g i j := by
  simp only [tensorPow, Matrix.of_apply]
  refine continuous_finsetProd _ fun x _ => ?_
  have h1 : Continuous fun g => (U g : Matrix (Fin N) (Fin N) ℂ) := continuous_subtype_val.comp hU
  exact (continuous_apply (j x)).comp ((continuous_apply (i x)).comp h1)

theorem avg_apply {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ) (i j : Fin d → Fin N) :
    averagingOperator μ U d i j = ∫ g, tensorPow U d g i j ∂μ := by
  letI : NormedAddCommGroup (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) :=
    Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) := Matrix.normedSpace
  have hc : Continuous fun g => tensorPow U d g := by
    refine continuous_pi fun a => continuous_pi fun b => tensorPow_cont U hU d a b
  have hint := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  let L : Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have := ContinuousLinearMap.integral_comp_comm L hint
  exact this.symm

theorem tp_int {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ) (i j : Fin d → Fin N) :
    Integrable (fun g => tensorPow U d g i j) μ :=
  (tensorPow_cont U hU d i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sum_int_mul {G : Type*} [MeasurableSpace G] (μ : Measure G) {ι : Type*} [Fintype ι]
    (f : ι → G → ℂ) (hf : ∀ j, Integrable (f j) μ) (c : ι → ℂ) :
    ∑ j, (∫ g, f j g ∂μ) * c j = ∫ g, ∑ j, f j g * c j ∂μ := by
  rw [integral_finsetSum _ (fun j _ => (hf j).mul_const (c j))]
  exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm

section
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ)

include hU in
theorem avg_left (h : G) : tensorPow U d h * averagingOperator μ U d = averagingOperator μ U d := by
  ext i k
  rw [Matrix.mul_apply]
  have h1 : ∀ j, tensorPow U d h i j * averagingOperator μ U d j k
      = ∫ g, tensorPow U d h i j * tensorPow U d g j k ∂μ := by
    intro j; rw [avg_apply μ U hU, integral_const_mul]
  rw [Finset.sum_congr rfl (fun j _ => h1 j),
    ← integral_finsetSum _ (fun j _ => (tp_int μ U hU d j k).const_mul _)]
  have h2 : ∀ g, ∑ j, tensorPow U d h i j * tensorPow U d g j k = tensorPow U d (h * g) i k := by
    intro g; rw [tensorPow_mul', Matrix.mul_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), avg_apply μ U hU]
  exact integral_mul_left_eq_self (fun g => tensorPow U d g i k) h

include hU in
theorem avg_idem : averagingOperator μ U d * averagingOperator μ U d = averagingOperator μ U d := by
  ext i k
  rw [Matrix.mul_apply]
  have h1 : ∀ j, averagingOperator μ U d i j * averagingOperator μ U d j k
      = ∫ g, tensorPow U d g i j * averagingOperator μ U d j k ∂μ := by
    intro j; rw [avg_apply μ U hU d i j, integral_mul_const]
  rw [Finset.sum_congr rfl (fun j _ => h1 j),
    ← integral_finsetSum _ (fun j _ => (tp_int μ U hU d i j).mul_const _)]
  have h2 : ∀ g, ∑ j, tensorPow U d g i j * averagingOperator μ U d j k = averagingOperator μ U d i k := by
    intro g
    have := congrFun (congrFun (avg_left μ U hU d g) i) k
    rwa [Matrix.mul_apply] at this
  rw [integral_congr_ae (Filter.Eventually.of_forall h2)]
  simp

include hU in
theorem avg_herm : (averagingOperator μ U d)ᴴ = averagingOperator μ U d := by
  have key : (averagingOperator μ U d)ᴴ * averagingOperator μ U d = averagingOperator μ U d := by
    ext i k
    rw [Matrix.mul_apply]
    have e1 : ∀ j, (averagingOperator μ U d)ᴴ i j = ∫ g, tensorPow U d g⁻¹ i j ∂μ := by
      intro j
      rw [Matrix.conjTranspose_apply, avg_apply μ U hU]
      change (starRingEnd ℂ) _ = _
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      exact tensorPow_inv_apply U d g i j
    have h1 : ∀ j, (averagingOperator μ U d)ᴴ i j * averagingOperator μ U d j k
        = ∫ g, tensorPow U d g⁻¹ i j * averagingOperator μ U d j k ∂μ := by
      intro j; rw [e1, integral_mul_const]
    have hi : ∀ j, Integrable (fun g => tensorPow U d g⁻¹ i j) μ := by
      intro j
      refine ((tensorPow_cont U hU d i j).comp continuous_inv).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [Finset.sum_congr rfl (fun j _ => h1 j),
      ← integral_finsetSum _ (fun j _ => (hi j).mul_const _)]
    have h2 : ∀ g, ∑ j, tensorPow U d g⁻¹ i j * averagingOperator μ U d j k = averagingOperator μ U d i k := by
      intro g
      have := congrFun (congrFun (avg_left μ U hU d g⁻¹) i) k
      rwa [Matrix.mul_apply] at this
    rw [integral_congr_ae (Filter.Eventually.of_forall h2)]
    simp
  have := congrArg Matrix.conjTranspose key
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, key] at this
  exact this.symm

include hU in
theorem avg_range : LinearMap.range (averagingOperator μ U d).mulVecLin = invariants U d := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩ h
    show (tensorPow U d h).mulVec ((averagingOperator μ U d).mulVec s) = (averagingOperator μ U d).mulVec s
    rw [Matrix.mulVec_mulVec, avg_left μ U hU d h]
  · intro ht
    refine ⟨t, ?_⟩
    show (averagingOperator μ U d).mulVec t = t
    funext i
    have h1 : ∀ j, averagingOperator μ U d i j * t j = ∫ g, tensorPow U d g i j * t j ∂μ := by
      intro j; rw [avg_apply μ U hU d i j, integral_mul_const]
    have h2 : ∀ g, ∑ j, tensorPow U d g i j * t j = t i := by
      intro g
      have := congrFun (ht g) i
      rwa [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mulVec, dotProduct, Finset.sum_congr rfl (fun j _ => h1 j),
      ← integral_finsetSum _ (fun j _ => (tp_int μ U hU d i j).mul_const _),
      integral_congr_ae (Filter.Eventually.of_forall h2)]
    simp

end

end WeingartenCalc.Fundamental

open WeingartenCalc.Fundamental

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ) :
    (averagingOperator μ U d)ᴴ = averagingOperator μ U d ∧
      averagingOperator μ U d * averagingOperator μ U d = averagingOperator μ U d ∧
      LinearMap.range (averagingOperator μ U d).mulVecLin = invariants U d :=
  ⟨avg_herm μ U hU d, avg_idem μ U hU d, avg_range μ U hU d⟩
