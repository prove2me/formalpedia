-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.polar_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:39.328283+00:00
-- url     : https://prove2.me/submissions/8d73fd54-c8c4-4237-98e6-827cf7d8a61f

import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereProb_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_pair
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_radJ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_radK
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_polar
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_polar
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_volumeIoiPow
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radJ_pos
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphere_linear_zero_null

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
private lemma log_norm_sum_smul_sphere_mul_exp_eq {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (z : UnitSphereC n) (r : ℝ) (hr : 0 < r)
    (hz : ∑ i, WithLp.ofLp c i * spherePoint z i ≠ 0) :
    log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp (r • (z : EuclideanSpace ℂ (Fin n))) i‖ *
        exp (-‖r • (z : EuclideanSpace ℂ (Fin n))‖ ^ 2) =
      (log r + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-r ^ 2) := by
  have h1 : ∑ i, WithLp.ofLp c i * WithLp.ofLp (r • (z : EuclideanSpace ℂ (Fin n))) i =
      (r : ℂ) * ∑ i, WithLp.ofLp c i * spherePoint z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, spherePoint]
    ring
  have h2 : ‖r • (z : EuclideanSpace ℂ (Fin n))‖ = r := by
    rw [norm_smul, norm_eq_of_mem_sphere z, mul_one, Real.norm_of_nonneg hr.le]
  rw [h1, h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
    Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hz)]
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (hn : 0 < n) (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    Integrable (fun z : UnitSphereC n ↦ log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖)
        (sphereProb n) ∧
      ∫ z, log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(sphereProb n) =
        gaussLogC ‖c‖ / gaussOneC - radK (2 * n - 1) / radJ (2 * n - 1) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin n)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  have hk : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1 = 2 * n - 1 := by rw [hdim]
  have hk1 : 1 ≤ 2 * n - 1 := by omega
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; omega)
  have hJ : radJ (2 * n - 1) ≠ 0 := (radJ_pos _).ne'

  have h2n : ((Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℕ) : ENNReal) ≠ 0 := by
    rw [hdim]; exact Nat.cast_ne_zero.mpr (by omega)
  have hA0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero h2n (measure_ball_pos _ _ one_pos).ne'
  have hAtop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  haveI : IsFiniteMeasure (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := ⟨lt_top_iff_ne_top.mpr hAtop⟩
  have hA : ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal =
      (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) * (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 1) := by
    rw [Measure.toSphere_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def]
  have hApos : 0 < ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal := ENNReal.toReal_pos hA0 hAtop

  have hIe : ∫ x : EuclideanSpace ℂ (Fin n), exp (-‖x‖ ^ 2) = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal * radJ (2 * n - 1) := by
    have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℂ (Fin n))) (fun y : ℝ => exp (-y ^ 2))
    simp only [nsmul_eq_mul, smul_eq_mul] at h
    rw [h, hA, hk, radJ, mul_assoc]
  obtain ⟨s, hs, hGi, hIG0, hIe0⟩ := gauss_pair hn c hc
  have hae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere, ∑ i, WithLp.ofLp c i * spherePoint z i ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact sphere_linear_zero_null c hc

  have hinner : ∀ z : UnitSphereC n, ∑ i, WithLp.ofLp c i * spherePoint z i ≠ 0 →
      ∫ r : Ioi (0 : ℝ), log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp ((r : ℝ) • (z : EuclideanSpace ℂ (Fin n))) i‖ *
          exp (-‖(r : ℝ) • (z : EuclideanSpace ℂ (Fin n))‖ ^ 2)
        ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1)) =
      radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1) := by
    intro z hz
    calc _ = ∫ r : Ioi (0 : ℝ), (fun t : ℝ => (log t + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-t ^ 2)) (r : ℝ)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1)) :=
          integral_congr_ae (ae_of_all _ fun r => log_norm_sum_smul_sphere_mul_exp_eq c z r.1 r.2 hz)
      _ = ∫ t in Ioi (0 : ℝ), t ^ (2 * n - 1) * ((log t + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-t ^ 2)) := by
          rw [hk]
          exact integral_volumeIoiPow (2 * n - 1)
            (fun t : ℝ => (log t + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-t ^ 2))
      _ = ∫ t in Ioi (0 : ℝ), (t ^ (2 * n - 1) * log t * exp (-t ^ 2) +
            log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * (t ^ (2 * n - 1) * exp (-t ^ 2))) := by
          congr 1; funext t; ring
      _ = radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1) := by
          rw [integral_add (integrableOn_radK hk1) (Integrable.const_mul (integrableOn_radJ _) _),
            integral_const_mul] <;> rfl
  have hΦ := integrable_polar n hGi
  have hψint : Integrable (fun z : UnitSphereC n => radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1))
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
    refine hΦ.integral_prod_left.congr ?_
    filter_upwards [hae] with z hz
    exact hinner z hz
  have hLσ : Integrable (fun z : UnitSphereC n => log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
    refine ((hψint.sub (integrable_const (radK (2 * n - 1)))).div_const (radJ (2 * n - 1))).congr
      (ae_of_all _ fun z => ?_)
    simp only [Pi.sub_apply]
    rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hJ]
  have hIG : ∫ x : EuclideanSpace ℂ (Fin n), log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2) =
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal * radK (2 * n - 1) + (∫ z, log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere) * radJ (2 * n - 1) := by
    rw [integral_polar hn, integral_prod _ hΦ]
    calc _ = ∫ z, (radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1)) ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
            apply integral_congr_ae
            filter_upwards [hae] with z hz
            exact hinner z hz
      _ = _ := by
            rw [integral_add (integrable_const _) (hLσ.mul_const _), integral_mul_const]
            simp only [integral_const, smul_eq_mul, measureReal_def]
  have e1 := hIG.symm.trans hIG0
  have e2 := hIe.symm.trans hIe0
  have hgn : gaussOneC ^ n = gaussOneC * gaussOneC ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hg : gaussOneC ≠ 0 := by
    intro h0
    rw [hgn, h0, zero_mul, mul_zero] at e2
    exact (mul_pos hApos (radJ_pos _)).ne' e2
  rw [sphereProb_eq]
  refine ⟨hLσ.smul_measure (ENNReal.inv_ne_top.mpr hA0), ?_⟩
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  set A := ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal with hAdef
  set IL := ∫ z, log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hILdef
  have hA0' : A ≠ 0 := hApos.ne'
  have hIL : IL = (s * (gaussLogC ‖c‖ * gaussOneC ^ (n - 1)) - A * radK (2 * n - 1)) /
      radJ (2 * n - 1) := by
    rw [eq_div_iff hJ]
    linear_combination e1
  have hX : s * (gaussLogC ‖c‖ * gaussOneC ^ (n - 1)) / (A * radJ (2 * n - 1)) =
      gaussLogC ‖c‖ / gaussOneC := by
    rw [div_eq_div_iff (mul_ne_zero hA0' hJ) hg]
    linear_combination (-gaussLogC ‖c‖) * e2 - (gaussLogC ‖c‖ * s) * hgn
  rw [hIL, ← hX]
  field_simp <;> ring
end ReciprocityTheory.MultiplicativeHeights
