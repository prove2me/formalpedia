-- Prove2me | solution 1 for OnlineConvexOpt.BanditConvex.spherical_gradient_estimator_identity
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:41:20.04067+00:00
-- url     : https://prove2.me/submissions/85b0bd82-cf62-44c0-8673-f6c754d04709

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_SmoothedFunction
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

/-- The unit vector `e` of the one-dimensional Euclidean space. -/
noncomputable def aux_sgei_e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

/-- The fair coin on `Bool`. -/
noncomputable def aux_sgei_P : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance aux_sgei_prob : IsProbabilityMeasure aux_sgei_P :=
  ⟨by simp [aux_sgei_P, ENNReal.inv_two_add_inv_two]⟩

/-- The uniform random unit vector `±e`. -/
noncomputable def aux_sgei_U : Bool → EuclideanSpace ℝ (Fin 1) :=
  fun b => if b then aux_sgei_e else -aux_sgei_e

/-- The indicator of the single point `e`. -/
noncomputable def aux_sgei_f : EuclideanSpace ℝ (Fin 1) → ℝ :=
  Set.indicator {aux_sgei_e} (fun _ => 1)

lemma aux_sgei_norm_e : ‖aux_sgei_e‖ = 1 := by simp [aux_sgei_e]

lemma aux_sgei_e_ne : aux_sgei_e ≠ 0 := by
  intro h
  have := aux_sgei_norm_e
  rw [h, norm_zero] at this
  norm_num at this

lemma aux_sgei_eq_smul (v : EuclideanSpace ℝ (Fin 1)) : v = (v 0) • aux_sgei_e := by
  ext i
  fin_cases i
  simp [aux_sgei_e]

lemma aux_sgei_iso (L : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1)) :
    L aux_sgei_e = aux_sgei_e ∨ L aux_sgei_e = -aux_sgei_e := by
  have h1 : ‖L aux_sgei_e‖ = 1 := by rw [L.norm_map]; exact aux_sgei_norm_e
  have h2 := aux_sgei_eq_smul (L aux_sgei_e)
  rw [h2, norm_smul, aux_sgei_norm_e, mul_one, Real.norm_eq_abs] at h1
  rcases (abs_eq (zero_le_one' ℝ)).mp h1 with h | h
  · left; rw [h2, h, one_smul]
  · right; rw [h2, h, neg_one_smul]

lemma aux_sgei_map (g : Bool → EuclideanSpace ℝ (Fin 1)) :
    Measure.map g aux_sgei_P =
      (2 : ENNReal)⁻¹ • (Measure.dirac (g true) + Measure.dirac (g false)) := by
  have hg : Measurable g := Measurable.of_discrete
  rw [aux_sgei_P, Measure.map_smul, Measure.map_add _ _ hg, Measure.map_dirac' hg,
    Measure.map_dirac' hg]

lemma aux_sgei_unif : IsUniformOnUnitSphere aux_sgei_P aux_sgei_U := by
  refine ⟨Filter.Eventually.of_forall (fun b => ?_), fun L => ?_⟩
  · cases b <;> simp [aux_sgei_U, aux_sgei_norm_e]
  · rw [aux_sgei_map, aux_sgei_map]
    simp only [aux_sgei_U, if_true, Bool.false_eq_true, if_false]
    rcases aux_sgei_iso L with h | h
    · rw [map_neg, h]
    · rw [map_neg, h, neg_neg, add_comm]

lemma aux_sgei_smooth_zero (y : EuclideanSpace ℝ (Fin 1)) :
    SmoothedFunction aux_sgei_f 1 y = 0 := by
  unfold SmoothedFunction
  have hI : ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
      aux_sgei_f (y + (1 : ℝ) • v) = 0 := by
    apply integral_eq_zero_of_ae
    have hnull : volume ({aux_sgei_e - y} : Set (EuclideanSpace ℝ (Fin 1))) = 0 :=
      measure_singleton _
    have hae : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))),
        aux_sgei_f (y + (1 : ℝ) • v) = 0 := by
      rw [ae_iff]
      apply measure_mono_null _ hnull
      intro v hv
      simp only [Set.mem_setOf_eq] at hv
      simp only [Set.mem_singleton_iff]
      by_contra hne
      apply hv
      simp only [aux_sgei_f, one_smul, Set.indicator_apply, Set.mem_singleton_iff]
      rw [if_neg]
      intro h
      apply hne
      rw [← h]
      abel
    exact ae_restrict_of_ae hae
  rw [hI, mul_zero]

end OnlineConvexOpt.BanditConvex

open OnlineConvexOpt.BanditConvex

theorem solution : ¬ (∀ {n : ℕ} {Ω : Type} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n))
    (U : Ω → EuclideanSpace ℝ (Fin n)) (hU : IsUniformOnUnitSphere Prob U)
    (grad : EuclideanSpace ℝ (Fin n)) (hgrad : HasGradientAt (SmoothedFunction f δ) grad x)
    (hint : Integrable (fun ω => f (x + δ • U ω) • U ω) Prob),
    (∫ ω, f (x + δ • U ω) • U ω ∂Prob) = (δ / n) • grad) := by
  intro H
  have hgrad : HasGradientAt (SmoothedFunction aux_sgei_f 1) 0
      (0 : EuclideanSpace ℝ (Fin 1)) := by
    have : SmoothedFunction aux_sgei_f 1 = fun _ => 0 := funext aux_sgei_smooth_zero
    rw [this]
    exact hasGradientAt_const _ _
  have hint : Integrable
      (fun ω => aux_sgei_f (0 + (1 : ℝ) • aux_sgei_U ω) • aux_sgei_U ω) aux_sgei_P :=
    Integrable.of_finite
  have key := @H 1 Bool _ aux_sgei_P _ aux_sgei_f 1 one_pos 0 aux_sgei_U aux_sgei_unif 0
    hgrad hint
  rw [smul_zero] at key
  have hint1 : ∀ b : Bool, Integrable
      (fun ω => aux_sgei_f (0 + (1 : ℝ) • aux_sgei_U ω) • aux_sgei_U ω)
      (Measure.dirac b) := fun _ => Integrable.of_finite
  rw [aux_sgei_P, integral_smul_measure, integral_add_measure (hint1 true) (hint1 false),
    integral_dirac, integral_dirac] at key
  have hfe : aux_sgei_f aux_sgei_e = 1 := by simp [aux_sgei_f]
  have hfne : aux_sgei_f (-aux_sgei_e) = 0 := by
    simp only [aux_sgei_f, Set.indicator_apply, Set.mem_singleton_iff]
    rw [if_neg]
    intro h
    apply aux_sgei_e_ne
    have h2 : (2 : ℝ) • aux_sgei_e = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      simp
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  simp only [aux_sgei_U, if_true, Bool.false_eq_true, if_false, zero_add, one_smul, hfe,
    hfne, zero_smul, add_zero] at key
  have : (2 : ENNReal)⁻¹.toReal ≠ 0 := by simp
  exact aux_sgei_e_ne ((smul_eq_zero.mp key).resolve_left this)
