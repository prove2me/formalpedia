-- Prove2me | solution 1 for WassersteinDRO.Guarantees.finite_sample_guarantees_ii
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:33:39.349433+00:00
-- url     : https://prove2.me/submissions/a3600404-5325-4ac3-9139-06e985efeae1

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_empiricalDistribution
import Definitions.Def_WassersteinDRO_Guarantees_nominalRisk
import Definitions.Def_WassersteinDRO_Guarantees_gelbrichRisk
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure

open MeasureTheory

namespace WassersteinDRO.Guarantees

lemma aux_fsg2_psdSqrt_zero {m : ℕ} : psdSqrt (0 : Matrix (Fin m) (Fin m) ℝ) = 0 := by
  unfold psdSqrt
  have h : ∃ B : Matrix (Fin m) (Fin m) ℝ, B.PosSemidef ∧ B * B = 0 :=
    ⟨0, Matrix.PosSemidef.zero, by simp⟩
  rw [dif_pos h]
  obtain ⟨hB, hBB⟩ := h.choose_spec
  have : Matrix.conjTranspose h.choose * h.choose = 0 := by rw [hB.1.eq]; exact hBB
  exact Matrix.conjTranspose_mul_self_eq_zero.mp this

lemma aux_fsg2_mean_dirac {m : ℕ} (ξ : EuclideanSpace ℝ (Fin m)) :
    meanVector (Measure.dirac ξ) = ξ := by
  unfold meanVector
  exact integral_dirac _ _

lemma aux_fsg2_cov_dirac {m : ℕ} (ξ : EuclideanSpace ℝ (Fin m)) :
    covarianceMatrix (Measure.dirac ξ) = 0 := by
  unfold covarianceMatrix
  rw [aux_fsg2_mean_dirac]
  ext i j
  simp [integral_dirac]

lemma aux_fsg2_emp_one {m : ℕ} (ξhat : Fin 1 → EuclideanSpace ℝ (Fin m)) :
    empiricalDistribution ξhat = Measure.dirac (ξhat 0) := by
  unfold empiricalDistribution
  simp

lemma aux_fsg2_norm_le (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ≤ ‖x 0‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]

lemma aux_fsg2_bound (ε : ℝ) (hε : 0 ≤ ε) (ξ : EuclideanSpace ℝ (Fin 1)) :
    gelbrichRisk ε Set.univ ξ 0 (fun x => x 0) ≤ ((ξ 0 + ε : ℝ) : EReal) := by
  unfold gelbrichRisk
  refine iSup_le fun Q => iSup_le fun hQ => iSup_le fun hI => ?_
  rw [EReal.coe_le_coe_iff]
  obtain ⟨-, -, hPSD, hU⟩ := hQ
  simp only [aux_fsg2_psdSqrt_zero, zero_mul, mul_zero, zero_add, smul_zero, sub_zero] at hU
  have htr := hPSD.trace_nonneg
  have h1 : ‖ξ - meanVector Q‖ ^ 2 ≤ ε ^ 2 := by linarith
  have h2 : ‖ξ - meanVector Q‖ ≤ ε :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).mp h1
  have h3 : ‖(ξ - meanVector Q) 0‖ ≤ ‖ξ - meanVector Q‖ := PiLp.norm_apply_le _ 0
  rw [Real.norm_eq_abs] at h3
  have hid : Integrable (fun x : EuclideanSpace ℝ (Fin 1) => x) Q := by
    refine hI.mono continuous_id.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa using aux_fsg2_norm_le x
  have h4 : nominalRisk Q (fun x => x 0) = (meanVector Q) 0 := by
    unfold nominalRisk meanVector
    have := (EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).integral_comp_comm hid
    simpa using this
  rw [h4]
  have h5 := neg_abs_le ((ξ - meanVector Q) 0)
  rw [PiLp.sub_apply] at h5 h3
  linarith

end WassersteinDRO.Guarantees

open WassersteinDRO.Guarantees

theorem solution : ¬ (∀ {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ) (α A c : ℝ)
    (hα : 2 < α) (hA : 0 < A) (hc : c > 1)
    (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ)
    (hP : IsProbabilityMeasure P) (hN : 0 < N)
    (hμ : meanVector P = μ) (hSigma : covarianceMatrix P = Sigma)
    (hInt : Integrable (fun x => Real.exp (‖x‖ ^ α)) P)
    (hA' : (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A)
    (Ξ : Set (EuclideanSpace ℝ (Fin m))) (hΞ : P Ξᶜ = 0)
    (L : Set (EuclideanSpace ℝ (Fin m) → ℝ)) (hLInt : ∀ ℓ ∈ L, Integrable ℓ P)
    (η ε : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hε : ε ≥ Real.log (c / η) / Real.sqrt N),
    sampleMeasure P N
        {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
          ∀ ℓ ∈ L, (nominalRisk P ℓ : EReal) ≤
            gelbrichRisk ε Ξ (meanVector (empiricalDistribution ξhat))
              (covarianceMatrix (empiricalDistribution ξhat)) ℓ} ≥
      ENNReal.ofReal (1 - η)) := by
  intro h
  set a : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 10 with ha
  set b : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (-10) with hb
  set P : Measure (EuclideanSpace ℝ (Fin 1)) :=
    (2 : ENNReal)⁻¹ • (Measure.dirac a + Measure.dirac b) with hPdef
  have hPprob : IsProbabilityMeasure P := by
    constructor
    simp only [hPdef, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  have := hPprob
  have hintP : ∀ f : EuclideanSpace ℝ (Fin 1) → ℝ, Integrable f P := by
    intro f
    refine Integrable.smul_measure ?_ (by simp)
    exact (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))
  set ℓ0 : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => x 0 with hℓ0
  have hnom : nominalRisk P ℓ0 = 0 := by
    unfold nominalRisk
    rw [hPdef, integral_smul_measure,
      integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
      integral_dirac, integral_dirac]
    simp [ha, hb, hℓ0]
  have hε7 : (7 : ℝ) ≥ Real.log (2 / (1 / 4)) / Real.sqrt ((1 : ℕ) : ℝ) := by
    rw [Nat.cast_one, Real.sqrt_one, div_one]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / (1 / 4) by norm_num)
    norm_num at this ⊢
    linarith
  have hI0 : 0 ≤ ∫ x, Real.exp (‖x‖ ^ (3 : ℝ)) ∂P :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have key := @h 1 (meanVector P) (covarianceMatrix P) 3
    ((∫ x, Real.exp (‖x‖ ^ (3 : ℝ)) ∂P) + 1) 2 (by norm_num)
    (by linarith)
    (by norm_num) P 1 hPprob one_pos rfl rfl (hintP _) (by linarith) Set.univ (by simp)
    {ℓ0} (by rintro ℓ rfl; exact hintP _) (1 / 4) 7 (by norm_num) (by norm_num) hε7
  set S : Set (EuclideanSpace ℝ (Fin 1)) := {x | -7 ≤ x 0} with hS
  have hsub : {ξhat : Fin 1 → EuclideanSpace ℝ (Fin 1) |
          ∀ ℓ ∈ ({ℓ0} : Set (EuclideanSpace ℝ (Fin 1) → ℝ)), (nominalRisk P ℓ : EReal) ≤
            gelbrichRisk 7 Set.univ (meanVector (empiricalDistribution ξhat))
              (covarianceMatrix (empiricalDistribution ξhat)) ℓ} ⊆
      Set.univ.pi (fun _ => S) := by
    intro ξhat hξ i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h1 := hξ ℓ0 rfl
    rw [hnom, aux_fsg2_emp_one, aux_fsg2_mean_dirac, aux_fsg2_cov_dirac] at h1
    have h2 := h1.trans (aux_fsg2_bound 7 (by norm_num) (ξhat 0))
    have h3 : (0 : ℝ) ≤ ξhat 0 0 + 7 := by exact_mod_cast h2
    show -7 ≤ ξhat 0 0
    linarith
  have hmeas : sampleMeasure P 1 (Set.univ.pi (fun _ => S)) = 2⁻¹ := by
    unfold sampleMeasure
    rw [Measure.pi_pi, Fin.prod_univ_one]
    simp only [hPdef, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
    rw [Measure.dirac_apply, Measure.dirac_apply]
    have haS : a ∈ S := by simp [hS, ha]; norm_num
    have hbS : b ∉ S := by simp [hS, hb]; norm_num
    simp [Set.indicator_of_mem haS, Set.indicator_of_notMem hbS]
  have hle := key.trans (measure_mono hsub)
  rw [hmeas] at hle
  have : ENNReal.ofReal (1 - 1 / 4) ≤ ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    simpa using hle
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this
