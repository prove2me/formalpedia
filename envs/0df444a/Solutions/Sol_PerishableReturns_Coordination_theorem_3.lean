-- Prove2me | solution 1 for PerishableReturns.Coordination.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T02:20:16.480587+00:00
-- url     : https://prove2.me/submissions/08f8e75a-80f0-4a67-a4eb-d5e618eade5b

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

set_option autoImplicit false

namespace PRCoord53d

open MeasureTheory ProbabilityTheory PerishableReturns.Coordination

lemma int_min (D : Measure ℝ) [IsProbabilityMeasure D] (hX : Integrable (fun x : ℝ => x) D)
    (Q : ℝ) : Integrable (fun x : ℝ => min x Q) D :=
  hX.inf (integrable_const Q)

lemma lin_int (D : Measure ℝ) [IsProbabilityMeasure D] (hX : Integrable (fun x : ℝ => x) D)
    (A B C Q : ℝ) :
    ∫ x, ((A * min x Q + B) - C * x) ∂D = A * (∫ x, min x Q ∂D) + B - C * (∫ x, x ∂D) := by
  have i1 : Integrable (fun x : ℝ => A * min x Q + B) D :=
    ((int_min D hX Q).const_mul _).add (integrable_const _)
  have i2 : Integrable (fun x : ℝ => C * x) D := hX.const_mul _
  have e2 : ∫ x, C * x ∂D = C * ∫ x, x ∂D := integral_const_mul C (fun x => x)
  rw [integral_sub i1 i2, e2,
    integral_add ((int_min D hX Q).const_mul _) (integrable_const _), integral_const_mul,
    integral_const]
  simp

lemma EPT_eq (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hX : Integrable (fun x : ℝ => x) D) (Q : ℝ) :
    EPT K D Q = (K.c3 - K.c) * Q + (K.p + K.g2 - K.c3) * (∫ x, min x Q ∂D)
      - K.g2 * (∫ x, x ∂D) := by
  unfold EPT
  rw [integral_congr_ae (g := fun x => ((K.p + K.g2 - K.c3) * min x Q + K.c3 * Q) - K.g2 * x)
    (Filter.Eventually.of_forall fun x => ?_)]
  · rw [lin_int D hX]
    ring
  · simp only [min_def]
    split_ifs <;> ring

lemma ae_pos (D : Measure ℝ) [NullSingletonClass D] (h : D (Set.Iio 0) = 0) :
    ∀ᵐ x ∂D, (0 : ℝ) < x := by
  rw [ae_iff]
  have hs : {x : ℝ | ¬ (0 : ℝ) < x} = Set.Iio 0 ∪ {0} := by
    ext x
    simp only [Set.mem_setOf_eq, not_lt, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
    exact le_iff_lt_or_eq
  rw [hs]
  exact measure_union_null h (measure_singleton 0)

lemma EPR_eq (K : Costs) (c1 c2 : ℝ) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hX : Integrable (fun x : ℝ => x) D) (hpos : ∀ᵐ x ∂D, (0 : ℝ) < x) (Q : ℝ) :
    EPR K c1 c2 1 D Q = (c2 - c1) * Q + (K.p + K.g - c2) * (∫ x, min x Q ∂D)
      - K.g * (∫ x, x ∂D) := by
  unfold EPR
  rw [integral_congr_ae (g := fun x => ((K.p + K.g - c2) * min x Q + c2 * Q) - K.g * x)
    (hpos.mono fun x hx => ?_)]
  · rw [lin_int D hX]
    ring
  · simp only [sub_self, zero_mul, min_def]
    rw [if_neg (not_le.mpr hx)]
    split_ifs <;> ring

lemma opt_affine (f g : ℝ → ℝ) (k C : ℝ) (hk : 0 < k) (h : ∀ Q, f Q = k * g Q + C) (Q : ℝ) :
    IsOptimalOrder f Q ↔ IsOptimalOrder g Q := by
  simp only [IsOptimalOrder, isMaxOn_iff, h]
  refine and_congr_right fun _ => forall₂_congr fun y _ => ?_
  constructor
  · intro hy
    nlinarith
  · intro hy
    nlinarith

end PRCoord53d

open MeasureTheory ProbabilityTheory PerishableReturns.Coordination in
theorem solution (K : Costs) (c1 : ℝ) (hc : K.c < c1) (hp : c1 < K.p) :
    ∃ c2 : ℝ, K.c3 < c2 ∧ c2 < c1 ∧
      c1 = (K.p + K.g) - (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3) ∧
      ∀ D : Measure ℝ, IsDemand D → NullSingletonClass D → Coordinates K c1 c2 1 D := by
  have hg := K.g_nonneg
  have hg1 := K.g1_nonneg
  have h3 := K.c3_lt_c
  have hcp := K.c_lt_p
  have hg2 : K.g2 = K.g + K.g1 := rfl
  have hb : 0 < K.p + K.g2 - K.c3 := by rw [hg2]; linarith
  have hd : 0 < K.p + K.g2 - K.c := by rw [hg2]; linarith
  have hu : 0 < K.p + K.g - c1 := by linarith
  have hbd : K.p + K.g2 - K.c < K.p + K.g2 - K.c3 := by linarith
  refine ⟨K.p + K.g - (K.p + K.g - c1) * (K.p + K.g2 - K.c3) / (K.p + K.g2 - K.c),
    ?_, ?_, ?_, ?_⟩
  · have key : (K.p + K.g - c1) * (K.p + K.g2 - K.c3)
        < (K.p + K.g - K.c3) * (K.p + K.g2 - K.c) := by
      rw [hg2]
      nlinarith [mul_pos (sub_pos.2 hc) hb, mul_nonneg hg1 (le_of_lt (sub_pos.2 h3))]
    have : (K.p + K.g - c1) * (K.p + K.g2 - K.c3) / (K.p + K.g2 - K.c) < K.p + K.g - K.c3 := by
      rw [div_lt_iff₀ hd]
      exact key
    linarith
  · have : K.p + K.g - c1 < (K.p + K.g - c1) * (K.p + K.g2 - K.c3) / (K.p + K.g2 - K.c) := by
      rw [lt_div_iff₀ hd]
      nlinarith [mul_lt_mul_of_pos_left hbd hu]
    linarith
  · field_simp
    ring
  · intro D hD hns
    haveI := hD.isProb
    have hX := hD.integrable
    have hpos := PRCoord53d.ae_pos D hD.nonneg
    intro Q
    apply PRCoord53d.opt_affine _ _ ((K.p + K.g - c1) / (K.p + K.g2 - K.c))
      (-K.g * (∫ x, x ∂D) + (K.p + K.g - c1) / (K.p + K.g2 - K.c) * K.g2 * (∫ x, x ∂D))
      (div_pos hu hd)
    intro Q'
    rw [PRCoord53d.EPR_eq K _ _ D hX hpos, PRCoord53d.EPT_eq K D hX]
    field_simp
    ring
