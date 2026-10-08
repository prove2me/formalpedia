-- Prove2me | solution 1 for RobustGeneralization.GaussLower.zbar_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:19:37.780388+00:00
-- url     : https://prove2.me/submissions/6fb2a6d9-29c2-4c91-9569-be122f6ccd79

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZbarAux

open RobustGeneralization.GaussLower

lemma pi_gaussVec (d n : ℕ) (θ : E d) (σ : ℝ) :
    Measure.pi (fun _ : Fin n => gaussVec θ σ) =
      (Measure.pi fun _ : Fin n => stdGaussian (E d)).map (fun v i => θ + σ • v i) := by
  unfold gaussVec
  exact (Measure.pi_map_pi (μ := fun _ : Fin n => stdGaussian (E d))
    (f := fun _ (v : E d) => θ + σ • v) (fun i => by fun_prop)).symm

lemma measurable_kernel (d n : ℕ) (σ : ℝ) :
    Measurable (fun θ : E d =>
      (Measure.pi fun _ : Fin n => stdGaussian (E d)).map (fun v i => θ + σ • v i)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hg : Measurable (fun p : E d × (Fin n → E d) => fun i => p.1 + σ • p.2 i) := by
    fun_prop
  have := measurable_measure_prodMk_left
    (ν := Measure.pi fun _ : Fin n => stdGaussian (E d)) (hg hs)
  convert this using 2 with θ
  rw [Measure.map_apply (by fun_prop) hs]
  rfl

lemma kernel_map_mean (d n : ℕ) (θ : E d) (σ : ℝ) (hn : (n : ℝ) ≠ 0) :
    ((Measure.pi fun _ : Fin n => stdGaussian (E d)).map (fun v i => θ + σ • v i)).map
      (fun z => ((n : ℝ)⁻¹) • ∑ i, z i)
    = ((Measure.pi fun _ : Fin n => stdGaussian (E d)).map
        (fun v => (σ / n) • ∑ i, v i)).map (fun y => θ + y) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext v
  simp only [Function.comp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.smul_sum, smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [inv_mul_cancel₀ hn, one_smul, div_eq_inv_mul]

lemma marginal_eq_conv (d n : ℕ) (σ : ℝ) (hn : (n : ℝ) ≠ 0) :
    (sampleMarginal d n σ).map (fun z => ((n : ℝ)⁻¹) • ∑ i, z i) =
      (stdGaussian (E d)) ∗ ((Measure.pi fun _ : Fin n => stdGaussian (E d)).map
        (fun v => (σ / n) • ∑ i, v i)) := by
  ext s hs
  have hmeas : Measurable (fun z : Fin n → E d => ((n : ℝ)⁻¹) • ∑ i, z i) := by fun_prop
  rw [Measure.map_apply hmeas hs, sampleMarginal]
  simp only [pi_gaussVec]
  rw [Measure.bind_apply (hmeas hs) (measurable_kernel d n σ).aemeasurable]
  rw [Measure.conv, Measure.map_apply measurable_add hs, Measure.prod_apply (measurable_add hs)]
  refine lintegral_congr fun θ => ?_
  rw [← Measure.map_apply hmeas hs, kernel_map_mean d n θ σ hn, Measure.map_apply (by fun_prop) hs]
  rfl

end ZbarAux

open RobustGeneralization.GaussLower in
theorem solution (d n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 < σ) :
    (sampleMarginal d n σ).map (fun z => ((n : ℝ)⁻¹) • ∑ i, z i) =
      gaussVec 0 (Real.sqrt (1 + σ ^ 2 / n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [ZbarAux.marginal_eq_conv d n σ hn']
  unfold gaussVec
  simp only [zero_add]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_stdGaussian, charFun_map_smul_comp (by fun_prop),
    charFun_map_sum_pi_eq_prod, Finset.prod_apply]
  simp only [charFun_stdGaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [charFun_map_smul, charFun_stdGaussian, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have key : -‖t‖ ^ 2 / 2 + (n : ℝ) * (-(|σ / n| * ‖t‖) ^ 2 / 2) =
      -(|Real.sqrt (1 + σ ^ 2 / n)| * ‖t‖) ^ 2 / 2 := by
    rw [mul_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  exact_mod_cast key
