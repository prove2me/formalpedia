-- Prove2me | solution 1 for RobustGeneralization.GaussLower.eq3_posterior_predictive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:07:23.333289+00:00
-- url     : https://prove2.me/submissions/96ecd046-1f89-475d-8f8d-851a0e4fcb56

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

lemma aux_ppd_gaussVec_eq_map {d : ℕ} (θ : E d) (σ : ℝ) :
    gaussVec θ σ = ((stdGaussian (E d)).map (fun v => σ • v)).map (fun y => θ + y) := by
  unfold gaussVec
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

instance aux_ppd_isProb_gaussVec {d : ℕ} (θ : E d) (σ : ℝ) :
    IsProbabilityMeasure (gaussVec θ σ) := by
  unfold gaussVec
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma aux_ppd_charFun_gaussVec {d : ℕ} (m : E d) (s : ℝ) (t : E d) :
    charFun (gaussVec m s) t =
      Complex.exp (-(‖s • t‖ ^ 2 / 2 : ℝ)) * Complex.exp (inner ℝ m t * Complex.I) := by
  rw [aux_ppd_gaussVec_eq_map, charFun_map_const_add, charFun_map_smul, charFun_stdGaussian]
  push_cast
  ring_nf

lemma aux_ppd_meas_translate {d : ℕ} (ν : Measure (E d)) [SFinite ν] (f : E d → E d)
    (hf : Measurable f) : Measurable (fun θ => ν.map (fun y => f θ + y)) := by
  refine Measure.measurable_of_measurable_coe _ (fun B hB => ?_)
  have h : ∀ θ, ν.map (fun y => f θ + y) B =
      ν (Prod.mk θ ⁻¹' ((fun p : E d × E d => f p.1 + p.2) ⁻¹' B)) := by
    intro θ
    rw [Measure.map_apply (by fun_prop) hB]
    rfl
  simp_rw [h]
  exact measurable_measure_prodMk_left (hB.preimage (by fun_prop))

lemma aux_ppd_bind_eq_conv {d : ℕ} (μ ν : Measure (E d)) [SFinite ν] (f : E d → E d)
    (hf : Measurable f) :
    μ.bind (fun θ => ν.map (fun y => f θ + y)) = (μ.map f) ∗ ν := by
  ext A hA
  rw [Measure.bind_apply hA (aux_ppd_meas_translate ν f hf).aemeasurable, Measure.conv,
    Measure.map_apply (by fun_prop) hA, Measure.prod_apply (hA.preimage (by fun_prop)),
    lintegral_map ?_ hf]
  · congr with θ
    rw [Measure.map_apply (by fun_prop) hA]
    rfl
  · exact measurable_measure_prodMk_left (hA.preimage (by fun_prop))

lemma aux_ppd_bind_gaussVec {d : ℕ} (m : E d) (s σ c : ℝ) (hc : c ^ 2 = 1) :
    (gaussVec m s).bind (fun θ => gaussVec (c • θ) σ) =
      gaussVec (c • m) (Real.sqrt (s ^ 2 + σ ^ 2)) := by
  simp_rw [aux_ppd_gaussVec_eq_map (c • _) σ]
  rw [aux_ppd_bind_eq_conv _ _ (fun θ => c • θ) (by fun_prop)]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_map_smul, charFun_map_smul, charFun_stdGaussian,
    aux_ppd_charFun_gaussVec, aux_ppd_charFun_gaussVec]
  have hr : Real.sqrt (s ^ 2 + σ ^ 2) ^ 2 = s ^ 2 + σ ^ 2 := Real.sq_sqrt (by positivity)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hc, one_mul, real_inner_smul_left,
    real_inner_smul_right, hr]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have habs : ((|σ| : ℝ) : ℂ) ^ 2 = (σ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  push_cast
  linear_combination (-(↑‖t‖ : ℂ) ^ 2 / 2) * habs

end RobustGeneralization.GaussLower

open RobustGeneralization.GaussLower
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {d : ℕ} (m : E d) (s σ : ℝ) (hs : 0 < s) (hσ : 0 < σ) :
    (gaussVec m s).bind (fun θ => gaussModel θ σ) =
      gaussModel m (Real.sqrt (s ^ 2 + σ ^ 2)) := by
  have h1 := aux_ppd_bind_gaussVec m s σ 1 (by norm_num)
  have h2 := aux_ppd_bind_gaussVec m s σ (-1) (by norm_num)
  simp only [one_smul, neg_smul] at h1 h2
  have hk1 : Measurable (fun θ : E d => gaussVec θ σ) := by
    simp_rw [aux_ppd_gaussVec_eq_map _ σ]
    exact aux_ppd_meas_translate _ id measurable_id
  have hk2 : Measurable (fun θ : E d => gaussVec (-θ) σ) := hk1.comp measurable_neg
  have key : ∀ (θ : E d) (σ : ℝ) (A : Set (E d × Bool)), MeasurableSet A →
      gaussModel θ σ A = 1 / 2 * gaussVec θ σ ((fun x : E d => (x, true)) ⁻¹' A)
        + 1 / 2 * gaussVec (-θ) σ ((fun x : E d => (x, false)) ⁻¹' A) := by
    intro θ σ A hA
    simp only [gaussModel, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Measure.map_apply (by fun_prop) hA, Measure.map_apply (by fun_prop) hA]
  have hmeas : Measurable fun θ : E d => gaussModel θ σ := by
    refine Measure.measurable_of_measurable_coe _ (fun B hB => ?_)
    simp_rw [key _ σ B hB]
    exact (((Measure.measurable_coe (hB.preimage (by fun_prop))).comp hk1).const_mul _).add
      (((Measure.measurable_coe (hB.preimage (by fun_prop))).comp hk2).const_mul _)
  ext A hA
  have hA1 : MeasurableSet ((fun x : E d => (x, true)) ⁻¹' A) := hA.preimage (by fun_prop)
  have hA2 : MeasurableSet ((fun x : E d => (x, false)) ⁻¹' A) := hA.preimage (by fun_prop)
  rw [Measure.bind_apply hA hmeas.aemeasurable, key m _ A hA]
  simp_rw [key _ σ A hA]
  rw [lintegral_add_left, lintegral_const_mul, lintegral_const_mul,
    ← Measure.bind_apply hA1 hk1.aemeasurable, ← Measure.bind_apply hA2 hk2.aemeasurable, h1, h2]
  · exact (Measure.measurable_coe hA2).comp hk2
  · exact (Measure.measurable_coe hA1).comp hk1
  · exact ((Measure.measurable_coe hA1).comp hk1).const_mul _
