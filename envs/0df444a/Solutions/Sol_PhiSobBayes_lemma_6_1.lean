-- Prove2me | solution 1 for PhiSobBayes.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:19:34.243731+00:00
-- url     : https://prove2.me/submissions/0ee9a00e-0878-48d5-b40a-057930b2676e

import Mathlib
import Definitions.Def_PhiSobBayes_IsLogConcave
import Definitions.Def_PhiSobBayes_IsStronglyLogConcave
import Definitions.Def_PhiSobBayes_posterior

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

lemma PSB61_hasFDerivAt_q {n : ℕ} (t : ℝ) (ht : 0 ≤ t) (y x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => ‖y - Real.sqrt t • x‖ ^ 2 / 2)
      (innerSL ℝ (t • x - Real.sqrt t • y)) x := by
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => y - Real.sqrt t • x)
      (-(Real.sqrt t • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) x := by
    have := ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt (x := x)).const_smul
      (Real.sqrt t)
    exact this.const_sub y
  have h2 := (h1.norm_sq).const_smul (1/2 : ℝ)
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) => ‖y - Real.sqrt t • x‖ ^ 2 / 2) =
      fun x => (1/2 : ℝ) • ‖y - Real.sqrt t • x‖ ^ 2 := by
    funext z
    simp only [smul_eq_mul]
    ring
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext v
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  simp
  linear_combination (inner ℝ x v) * hs

lemma PSB61_hasFDerivAt_lin {n : ℕ} (t : ℝ) (y x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => innerSL ℝ (t • x - Real.sqrt t • y))
      (t • innerSL ℝ) x := by
  have := ((t • innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] _).hasFDerivAt (x := x)).sub_const
    (innerSL ℝ (Real.sqrt t • y))
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) => innerSL ℝ (t • x - Real.sqrt t • y)) =
      fun x => (t • innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] _) x - innerSL ℝ (Real.sqrt t • y) := by
    funext z
    simp [map_sub, map_smul]
  rw [hfun]
  exact this

theorem solution {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : PhiSobBayes.IsLogConcave μ)
    (t : ℝ) (ht : 0 < t) (y : EuclideanSpace ℝ (Fin n)) :
    PhiSobBayes.IsStronglyLogConcave (PhiSobBayes.posterior μ t y) t := by
  obtain ⟨hprob, V, hV1, hV2, hV3, rfl⟩ := hμ
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => -‖y - Real.sqrt t • x‖ ^ 2 / 2 with hg
  set μ0 := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) with hμ0
  have hgc : Continuous g := by fun_prop
  have hint : Integrable (fun x => Real.exp (g x)) μ0 := by
    refine Integrable.of_bound (hgc.rexp.aestronglyMeasurable) 1 ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ ‖y - Real.sqrt t • x‖ ^ 2 := by positivity
    simp only [hg]
    linarith
  set Z := ∫ x, Real.exp (g x) ∂μ0 with hZ
  have hZpos : 0 < Z := integral_exp_pos hint
  have hpost : PhiSobBayes.posterior μ0 t y =
      μ0.withDensity (fun x => ENNReal.ofReal (Real.exp (g x) / Z)) := rfl
  rw [hpost]
  refine ⟨?_, fun x => V x + (‖y - Real.sqrt t • x‖ ^ 2 / 2 + Real.log Z), ?_⟩
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_div, ← hZ, div_self hZpos.ne', ENNReal.ofReal_one]
    · exact hint.div_const Z
    · exact Filter.Eventually.of_forall (fun x => by positivity)
  have hfd : fderiv ℝ (fun x => V x + (‖y - Real.sqrt t • x‖ ^ 2 / 2 + Real.log Z)) =
      fun x => fderiv ℝ V x + innerSL ℝ (t • x - Real.sqrt t • y) := by
    funext x
    exact ((hV1 x).hasFDerivAt.add ((PSB61_hasFDerivAt_q t ht.le y x).add_const _)).fderiv
  have hfd2 := fun x => (hV2 x).hasFDerivAt.add (PSB61_hasFDerivAt_lin t y x)
  refine ⟨fun x => ((hV1 x).hasFDerivAt.add
      ((PSB61_hasFDerivAt_q t ht.le y x).add_const _)).differentiableAt, ?_, ?_, ?_⟩
  · rw [hfd]; exact fun x => (hfd2 x).differentiableAt
  · intro x v
    rw [hfd, show (fun x => fderiv ℝ V x + innerSL ℝ (t • x - Real.sqrt t • y)) =
      (fderiv ℝ V + fun x => innerSL ℝ (t • x - Real.sqrt t • y)) from rfl, (hfd2 x).fderiv]
    have := hV3 x v
    simp
    have h3 : ((innerSL ℝ) v) v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    erw [h3]
    linarith
  · rw [hμ0, ← withDensity_mul]
    · congr 1
      funext x
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [hg]
      simp only
      rw [show -(V x + (‖y - Real.sqrt t • x‖ ^ 2 / 2 + Real.log Z)) =
        (-V x + -‖y - Real.sqrt t • x‖ ^ 2 / 2) - Real.log Z by ring]
      rw [Real.exp_sub, Real.exp_add, Real.exp_log hZpos, mul_div_assoc]
    · exact (hV1.continuous.neg.rexp).measurable.ennreal_ofReal
    · exact ((hgc.rexp).measurable.div_const Z).ennreal_ofReal
