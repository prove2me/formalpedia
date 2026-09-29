-- Prove2me | solution 1 for Weinberg1965.photon_log_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T03:51:19.997802+00:00
-- url     : https://prove2.me/submissions/ed99cb51-18d5-4f34-bb64-a307bed5c40c

import Mathlib
import Definitions.Def_Weinberg1965_Defs

open Weinberg1965

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W6_Weinberg1965_mdotNull_smul (m : ℝ) (p u : Vec3) (r : ℝ) (hr : 0 ≤ r) :
    mdotNull m p (r • u) = r * mdotNull m p u := by
  unfold mdotNull
  rw [inner_smul_right, norm_smul, Real.norm_of_nonneg hr]
  ring

theorem W6_Weinberg1965_radial (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam < Λ) :
    ∫ r, (Set.Icc lam Λ).indicator (fun r : ℝ => (r ^ 3)⁻¹) (r : ℝ)
      ∂(MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ Vec3 - 1)) = Real.log (Λ / lam) := by
  have hdim : Module.finrank ℝ Vec3 - 1 = 2 := by simp
  rw [hdim]
  simp only [MeasureTheory.Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    MeasureTheory.integral_subtype_comap measurableSet_Ioi
      (fun a : ℝ => Real.toNNReal (a ^ 2) • (Set.Icc lam Λ).indicator (fun r : ℝ => (r ^ 3)⁻¹) a)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (g := (Set.Icc lam Λ).indicator (fun a : ℝ => a⁻¹)) (fun a ha => ?_)]
  · rw [MeasureTheory.setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.2 (show Set.Icc lam Λ ⊆ Set.Ioi 0 from fun x hx => lt_of_lt_of_le hlam hx.1),
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlamΛ.le,
      integral_inv_of_pos hlam (hlam.trans hlamΛ)]
  · have ha' : (0 : ℝ) < a := ha
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), smul_eq_mul,
      Set.indicator_apply, Set.indicator_apply]
    split_ifs
    · field_simp
    · simp

theorem W6_Weinberg1965_polar (F : Vec3 → ℝ) :
    ∫ q, F q = ∫ y : Metric.sphere (0 : Vec3) 1 × Set.Ioi (0 : ℝ), F (((y.2 : ℝ)) • (y.1 : Vec3))
      ∂(MeasureTheory.volume.toSphere.prod
        (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ Vec3 - 1))) := by
  calc ∫ q, F q = ∫ x : ({(0 : Vec3)}ᶜ : Set Vec3), F x
        ∂(MeasureTheory.volume.comap Subtype.val) := by
        rw [MeasureTheory.integral_subtype_comap (measurableSet_singleton _).compl,
          MeasureTheory.restrict_compl_singleton]
    _ = _ := by
        rw [← (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
          MeasureTheory.volume).integral_comp (Homeomorph.measurableEmbedding _)]
        congr 1
        funext x
        have hx : ‖(x : Vec3)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
        congr 1
        simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
        rw [smul_smul, mul_inv_cancel₀ hx, one_smul]

theorem W6_Weinberg1965_shell (G : Vec3 → ℝ) (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam < Λ)
    (hG : ∀ r : ℝ, 0 < r → ∀ u : Vec3, ‖u‖ = 1 → G (r • u) = (r ^ 3)⁻¹ * G u) :
    ∫ q in {q : Vec3 | lam ≤ ‖q‖ ∧ ‖q‖ ≤ Λ}, G q =
      (∫ u : Metric.sphere (0 : Vec3) 1, G (u : Vec3) ∂(MeasureTheory.volume.toSphere)) *
        Real.log (Λ / lam) := by
  have hS : MeasurableSet {q : Vec3 | lam ≤ ‖q‖ ∧ ‖q‖ ≤ Λ} :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  rw [← MeasureTheory.integral_indicator hS, W6_Weinberg1965_polar]
  have hpt : ∀ y : Metric.sphere (0 : Vec3) 1 × Set.Ioi (0 : ℝ),
      ({q : Vec3 | lam ≤ ‖q‖ ∧ ‖q‖ ≤ Λ}).indicator G (((y.2 : ℝ)) • (y.1 : Vec3)) =
        G (y.1 : Vec3) * (Set.Icc lam Λ).indicator (fun r : ℝ => (r ^ 3)⁻¹) (y.2 : ℝ) := by
    rintro ⟨u, r⟩
    have hr : 0 < (r : ℝ) := r.2
    have hu : ‖(u : Vec3)‖ = 1 := by simp
    have hnorm : ‖(r : ℝ) • (u : Vec3)‖ = r := by
      rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hmem : lam ≤ (r : ℝ) ∧ (r : ℝ) ≤ Λ
    · have h1 : ((r : ℝ) • (u : Vec3)) ∈ {q : Vec3 | lam ≤ ‖q‖ ∧ ‖q‖ ≤ Λ} := by
        show lam ≤ ‖(r : ℝ) • (u : Vec3)‖ ∧ ‖(r : ℝ) • (u : Vec3)‖ ≤ Λ
        rw [hnorm]; exact hmem
      rw [if_pos h1, if_pos (show (r : ℝ) ∈ Set.Icc lam Λ from hmem), hG _ hr _ hu, mul_comm]
    · have h1 : ((r : ℝ) • (u : Vec3)) ∉ {q : Vec3 | lam ≤ ‖q‖ ∧ ‖q‖ ≤ Λ} := by
        show ¬ (lam ≤ ‖(r : ℝ) • (u : Vec3)‖ ∧ ‖(r : ℝ) • (u : Vec3)‖ ≤ Λ)
        rw [hnorm]; exact hmem
      rw [if_neg h1, if_neg (show (r : ℝ) ∉ Set.Icc lam Λ from hmem), mul_zero]
  simp_rw [hpt]
  rw [MeasureTheory.integral_prod_mul (fun u : Metric.sphere (0 : Vec3) 1 => G (u : Vec3))
    (fun r : Set.Ioi (0 : ℝ) => (Set.Icc lam Λ).indicator (fun r : ℝ => (r ^ 3)⁻¹) (r : ℝ)),
    W6_Weinberg1965_radial lam Λ hlam hlamΛ]

theorem solution {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1)
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam < Λ) :
    -(1 / (2 * (2 * Real.pi) ^ 3)) *
        ∫ q in {q : Vec3 | lam ≤ ‖q‖ ∧ ‖q‖ ≤ Λ}, (1 / ‖q‖) *
          ∑ n, ∑ k, e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
            (mdotNull (m n) (p n) q * mdotNull (m k) (p k) q)
      = -(photonIndex m p e η) * Real.log (Λ / lam) := by
  rw [W6_Weinberg1965_shell _ lam Λ hlam hlamΛ]
  · have hPI : photonIndex m p e η = 1 / (2 * (2 * Real.pi) ^ 3) *
        ∫ u : Metric.sphere (0 : Vec3) 1, (1 / ‖(u : Vec3)‖) *
          ∑ n, ∑ k, e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
            (mdotNull (m n) (p n) u * mdotNull (m k) (p k) u) ∂(MeasureTheory.volume.toSphere) := by
      unfold photonIndex solidAngleIntegral
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext u
      have hu : ‖(u : Vec3)‖ = 1 := by simp
      unfold photonAngular
      rw [hu, div_one, one_mul]
      congr 1
      simp only [mdotNull, hu, mul_one]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
      congr 1
      ring
    rw [hPI]
    ring
  · intro r hr u hu
    have hsum : (∑ n, ∑ k, e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
          (mdotNull (m n) (p n) (r • u) * mdotNull (m k) (p k) (r • u))) =
        (r ^ 2)⁻¹ * ∑ n, ∑ k, e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
          (mdotNull (m n) (p n) u * mdotNull (m k) (p k) u) := by
      simp only [W6_Weinberg1965_mdotNull_smul _ _ _ r hr.le]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum, norm_smul, hu, Real.norm_of_nonneg hr.le]
    ring

theorem W6_Weinberg1965_energy_gt (m : ℝ) (hm : 0 < m) (p u : Vec3) (hu : ‖u‖ = 1) :
    0 < energy m p - inner ℝ p u := by
  have h1 : inner ℝ p u ≤ ‖p‖ := by
    have := real_inner_le_norm p u
    rw [hu, mul_one] at this
    exact this
  have h2 : ‖p‖ < energy m p := by
    unfold energy
    rw [show ‖p‖ = Real.sqrt (‖p‖ ^ 2) from (Real.sqrt_sq (norm_nonneg p)).symm]
    apply Real.sqrt_lt_sqrt (by positivity)
    have := pow_pos hm 2
    rw [Real.sq_sqrt (by positivity)]
    linarith
  linarith

theorem W6_Weinberg1965_photonAngular_nonneg {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hcharge : ∑ n, η n * e n = 0) (u : Vec3) (hu : ‖u‖ = 1) :
    0 ≤ photonAngular m p e η u := by
  have ha : ∀ n, 0 < energy (m n) (p n) - inner ℝ (p n) u := fun n =>
    W6_Weinberg1965_energy_gt (m n) (hm n) (p n) u hu
  set a : ι → ℝ := fun n => energy (m n) (p n) - inner ℝ (p n) u with hadef
  set V : Vec3 := ∑ n, (η n * e n / a n) • p n with hV
  set V0 : ℝ := ∑ n, η n * e n * energy (m n) (p n) / a n with hV0
  have hVV : ‖V‖ ^ 2 = ∑ n, ∑ k, (η n * e n / a n) * (η k * e k / a k) * inner ℝ (p n) (p k) := by
    rw [← real_inner_self_eq_norm_sq, hV, sum_inner]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hV0sq : V0 ^ 2 = ∑ n, ∑ k, (η n * e n * energy (m n) (p n) / a n) *
      (η k * e k * energy (m k) (p k) / a k) := by
    rw [sq, hV0, Finset.sum_mul_sum]
  have hV0u : V0 = inner ℝ V u := by
    rw [hV0, hV, sum_inner]
    have : ∀ n, η n * e n * energy (m n) (p n) / a n =
        η n * e n + inner ℝ ((η n * e n / a n) • p n) u := by
      intro n
      rw [real_inner_smul_left]
      have hne : a n ≠ 0 := (ha n).ne'
      have hE : energy (m n) (p n) = a n + inner ℝ (p n) u := by simp only [hadef]; ring
      rw [hE]
      field_simp
      try ring
    rw [Finset.sum_congr rfl fun n _ => this n, Finset.sum_add_distrib, hcharge, zero_add]
  have hle : V0 ^ 2 ≤ ‖V‖ ^ 2 := by
    rw [hV0u]
    have := abs_real_inner_le_norm V u
    rw [hu, mul_one] at this
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  have hsum : ∑ n, ∑ k, e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
      ((energy (m n) (p n) - inner ℝ (p n) u) * (energy (m k) (p k) - inner ℝ (p k) u)) =
      ‖V‖ ^ 2 - V0 ^ 2 := by
    rw [hVV, hV0sq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold mdot
    simp only [hadef, div_eq_mul_inv, mul_inv]
    ring
  unfold photonAngular
  rw [hsum]
  have hc : 0 ≤ 1 / (2 * (2 * Real.pi) ^ 3) := by positivity
  exact mul_nonneg hc (by linarith)

theorem W6_Weinberg1965_photonIndex_nonneg {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1)
    (hcharge : ∑ n, η n * e n = 0) :
    0 ≤ photonIndex m p e η := by
  unfold photonIndex solidAngleIntegral
  refine MeasureTheory.integral_nonneg fun u => ?_
  exact W6_Weinberg1965_photonAngular_nonneg m p e η hm hcharge (u : Vec3) (by simp)
