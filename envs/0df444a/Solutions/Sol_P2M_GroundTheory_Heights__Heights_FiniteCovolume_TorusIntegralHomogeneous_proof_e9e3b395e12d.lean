-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusIntegralHomogeneous_proof_e9e3b395e12d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:29:24.286846+00:00
-- url     : https://prove2.me/submissions/b43409eb-a6ae-4dda-805c-6e96e69bc70a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusIntegralHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {κ : Type*} [Fintype κ]
private lemma weighted_sum_smul (q : κ → ℝ) (t : ℝ) (b : κ → ℂ) :
    ∑ i, q i * ‖(t • b) i‖ ^ 2 = t ^ 2 * ∑ i, q i * ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring
private lemma prod_smul (n : ℕ) {t : ℝ} (ht : 0 < t) (b : κ → ℂ) :
    ∏ i, ‖(t • b) i‖ₑ ^ (2 * n) =
      ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) * ∏ i, ‖b i‖ₑ ^ (2 * n) := by
  simp_rw [Pi.smul_apply, enorm_smul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul,
    Real.enorm_eq_ofReal ht.le, ENNReal.ofReal_pow ht.le]
private lemma indicator_smul (q : κ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) (b : κ → ℂ) :
    {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) (t • b) =
      ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) *
        {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b := by
  have hmem : (t • b) ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2} ↔
      b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} := by
    simp only [Set.mem_ofPred_eq, weighted_sum_smul, one_pow]
    exact mul_lt_iff_lt_one_right (by positivity)
  by_cases hb : b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}
  · rw [Set.indicator_of_mem (hmem.2 hb), Set.indicator_of_mem hb, prod_smul n ht]
  · rw [Set.indicator_of_notMem (fun h => hb (hmem.1 h)), Set.indicator_of_notMem hb, mul_zero]
private lemma measurable_integrand (q : κ → ℝ) (n : ℕ) (s : ℝ) :
    Measurable ({b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < s}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n))) := by
  refine Measurable.indicator ?_ ?_
  · exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).enorm.pow_const _
  · exact measurableSet_lt (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).norm.pow_const 2)) measurable_const
private lemma finrank_fun_complex : Module.finrank ℝ (κ → ℂ) = 2 * Fintype.card κ := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, mul_comm]
private lemma integral_scaling (q : κ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
      (∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b) *
        ENNReal.ofReal (t ^ ((2 * n + 2) * Fintype.card κ)) := by
  set g : (κ → ℂ) → ℝ≥0∞ := {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
    (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) with hg
  have hpt : ∀ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
        ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) * g (t⁻¹ • b) := by
    intro b
    have h := indicator_smul q n ht (t⁻¹ • b)
    rwa [smul_inv_smul₀ ht.ne'] at h
  have hmeas : Measurable g := measurable_integrand q n _
  have hmap : ∫⁻ b : κ → ℂ, g (t⁻¹ • b) =
      ENNReal.ofReal (t ^ (2 * Fintype.card κ)) * ∫⁻ b, g b := by
    rw [← lintegral_map hmeas (measurable_const_smul _),
      Measure.map_addHaar_smul volume (inv_ne_zero ht.ne'), lintegral_smul_measure,
      finrank_fun_complex, inv_pow, inv_inv, abs_of_pos (by positivity : 0 < t ^ (2 * Fintype.card κ)),
      smul_eq_mul]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    mul_comm, ← ENNReal.ofReal_mul (by positivity), ← pow_add]
  congr 3
  ring
end
end GroundTheory.Heights₂.Heights.FiniteCovolume
end

set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {κ : Type*} [Fintype κ]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace TorusIntegralHomogeneous
theorem _root_.solution (κ : Type*) [Fintype κ] :
    TorusIntegralHomogeneous.Statement κ := by
  intro q hq n
  refine ⟨∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b, ?_, ?_, fun t ht => integral_scaling q n ht⟩
  ·
    rw [lintegral_pos_iff_support (measurable_integrand q n _)]
    have hS : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => (hq i).le
    let V : Set (κ → ℂ) :=
      {b | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} ∩ ⋂ i, {b | b i ≠ 0}
    have hVo : IsOpen V :=
      (isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const)
    have hVne : V.Nonempty := by
      have hx : 0 < ((∑ i, q i) + 1)⁻¹ := by positivity
      have h1 : ‖((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ)‖ = ((∑ i, q i) + 1)⁻¹ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx.le]
      refine ⟨fun _ => ((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ), ?_, ?_⟩
      · show ∑ i, q i * ‖((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ)‖ ^ 2 < 1 ^ 2
        rw [h1, ← Finset.sum_mul, one_pow, inv_pow, ← div_eq_mul_inv,
          div_lt_one (by positivity)]
        nlinarith
      · exact Set.mem_iInter.2 fun i => Complex.ofReal_ne_zero.2 hx.ne'
    refine lt_of_lt_of_le (hVo.measure_pos volume hVne) (measure_mono ?_)
    rintro b ⟨hb1, hb2⟩
    rw [Function.mem_support, Set.indicator_of_mem hb1]
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      pow_ne_zero _ (enorm_ne_zero.2 (Set.mem_iInter.1 hb2 i))
  ·
    set R : ℝ := ∑ i, (q i)⁻¹ + 1 with hR
    have hR1 : 1 ≤ R := by
      have : 0 ≤ ∑ i, (q i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.2 (hq i)).le
      linarith
    have hbd : ∀ b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}, ∀ i, ‖b i‖ < R := by
      intro b hb i
      have hb' : ∑ j, q j * ‖b j‖ ^ 2 < 1 := by simpa using hb
      have hi : q i * ‖b i‖ ^ 2 < 1 :=
        lt_of_le_of_lt (Finset.single_le_sum (f := fun j => q j * ‖b j‖ ^ 2)
          (fun j _ => mul_nonneg (hq j).le (sq_nonneg _)) (Finset.mem_univ i)) hb'
      have hsq : ‖b i‖ ^ 2 < (q i)⁻¹ := by
        calc ‖b i‖ ^ 2 = (q i)⁻¹ * (q i * ‖b i‖ ^ 2) := by
              rw [← mul_assoc, inv_mul_cancel₀ (hq i).ne', one_mul]
          _ < (q i)⁻¹ * 1 := mul_lt_mul_of_pos_left hi (inv_pos.2 (hq i))
          _ = (q i)⁻¹ := mul_one _
      have hle : (q i)⁻¹ ≤ ∑ j, (q j)⁻¹ :=
        Finset.single_le_sum (f := fun j => (q j)⁻¹) (fun j _ => (inv_pos.2 (hq j)).le)
          (Finset.mem_univ i)
      have hx := norm_nonneg (b i)
      by_contra! h
      nlinarith
    have hsub : {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} ⊆ Metric.ball 0 R := by
      intro b hb
      rw [mem_ball_zero_iff, pi_norm_lt_iff (by linarith)]
      exact hbd b hb
    have hle : {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) ≤
        {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun _ => ∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) := by
      intro b
      by_cases hb : b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        refine Finset.prod_le_prod' fun i _ => pow_le_pow_left' ?_ _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbd b hb i).le
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    calc _ ≤ ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun _ => ∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) b := lintegral_mono hle
      _ ≤ (∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) *
          volume {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} := lintegral_indicator_const_le _ _
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.prod_lt_top fun i _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          (lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top)
end TorusIntegralHomogeneous
end GroundTheory.Heights₂.Heights.FiniteCovolume
