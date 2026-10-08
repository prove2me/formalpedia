-- Prove2me | solution 1 for SSDConstraint.Optimality.G_concave
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:03:50.573578+00:00
-- url     : https://prove2.me/submissions/1ad5b500-6b47-47f1-b1fa-0073cc813fc3

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem

set_option autoImplicit false

open MeasureTheory in
theorem d0339544_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
theorem d0339544_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    d0339544_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
  have h2 := integral_comp_neg_Ioi (0 : ℝ) (fun s => DualSSD.Shared.distFun μ X (s + x))
  rw [neg_zero] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, le_max_iff]
  have ht' : 0 < t := ht
  constructor
  · intro h; left; linarith
  · rintro (h | h)
    · linarith
    · linarith

theorem d0339544_pt (l a b η : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    max (η - (l * a + (1 - l) * b)) 0 ≤ l * max (η - a) 0 + (1 - l) * max (η - b) 0 := by
  have h1 : 0 ≤ 1 - l := by linarith
  have ha := le_max_left (η - a) 0
  have hb := le_max_left (η - b) 0
  have ha0 := le_max_right (η - a) 0
  have hb0 := le_max_right (η - b) 0
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left ha hl0, mul_le_mul_of_nonneg_left hb h1]
  · nlinarith [mul_nonneg hl0 ha0, mul_nonneg h1 hb0]

open MeasureTheory SSDConstraint.Optimality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω →₁[P] ℝ) (a b : ℝ) :
    ∀ X₁ X₂ : Ω →₁[P] ℝ, ∀ l ∈ Set.Icc (0 : ℝ) 1, ∀ η ∈ Set.Icc a b,
      l * (F2 P Y η - F2 P X₁ η) + (1 - l) * (F2 P Y η - F2 P X₂ η) ≤
        F2 P Y η - F2 P (l • X₁ + (1 - l) • X₂) η := by
  intro X₁ X₂ l hl η _
  simp only [F2]
  rw [d0339544_perf_eq P _ (L1.integrable_coeFn Y),
    d0339544_perf_eq P _ (L1.integrable_coeFn (l • X₁ + (1 - l) • X₂)),
    d0339544_perf_eq P _ (L1.integrable_coeFn X₁),
    d0339544_perf_eq P _ (L1.integrable_coeFn X₂)]
  have i1 : Integrable (fun ω => max (η - X₁ ω) 0) P :=
    ((integrable_const η).sub (L1.integrable_coeFn X₁)).pos_part
  have i2 : Integrable (fun ω => max (η - X₂ ω) 0) P :=
    ((integrable_const η).sub (L1.integrable_coeFn X₂)).pos_part
  have ic : Integrable (fun ω => max (η - (l • X₁ + (1 - l) • X₂) ω) 0) P :=
    ((integrable_const η).sub (L1.integrable_coeFn _)).pos_part
  have hae : (fun ω => (⇑(l • X₁ + (1 - l) • X₂)) ω) =ᵐ[P] fun ω => l * X₁ ω + (1 - l) * X₂ ω := by
    filter_upwards [Lp.coeFn_add (l • X₁) ((1 - l) • X₂), Lp.coeFn_smul l X₁,
      Lp.coeFn_smul (1 - l) X₂] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    simp [smul_eq_mul]
  have key : ∫ ω, max (η - (l • X₁ + (1 - l) • X₂) ω) 0 ∂P ≤
      l * ∫ ω, max (η - X₁ ω) 0 ∂P + (1 - l) * ∫ ω, max (η - X₂ ω) 0 ∂P := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul l) (i2.const_mul _)]
    apply integral_mono_ae ic ((i1.const_mul l).add (i2.const_mul _))
    filter_upwards [hae] with ω h
    rw [h]
    exact d0339544_pt l (X₁ ω) (X₂ ω) η hl.1 hl.2
  nlinarith [key]
