-- Prove2me | solution 1 for QuantumLTF.Example.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T19:53:37.693101+00:00
-- url     : https://prove2.me/submissions/3b1f38d7-ddc6-4c95-931f-a0d5515377b4

import Mathlib
import Definitions.Def_QuantumLTF_Example_HermiteModel

set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_roundCoord_error {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    |x-roundCoord M x| ≤ gridSpacing M := by
  have hδ : 0 < gridSpacing M := by
    dsimp [gridSpacing]
    positivity
  let u := (x+gridRadius M)/gridSpacing M
  have hlo := Int.floor_le u
  have hhi := Int.lt_floor_add_one u
  have hu : u*gridSpacing M = x+gridRadius M := by dsimp [u]; field_simp
  have hl := mul_le_mul_of_nonneg_right hlo hδ.le
  have hh := mul_lt_mul_of_pos_right hhi hδ
  change |x-(-gridRadius M+gridSpacing M*(⌊u⌋:ℝ))| ≤ gridSpacing M
  apply abs_le.mpr
  constructor <;> nlinarith

theorem section5_roundVec_error {n M : ℕ} (hM : 1 ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖x-roundVec M x‖ ≤ gridSpacing M * Real.sqrt n := by
  have hδ : 0 ≤ gridSpacing M := by dsimp [gridSpacing]; positivity
  have hsum : ‖x-roundVec M x‖^2 ≤ (n:ℝ)*(gridSpacing M)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin n, (gridSpacing M)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        change ‖x i-roundCoord M (x i)‖^2 ≤ (gridSpacing M)^2
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (section5_roundCoord_error hM _) 2
      _ = _ := by simp
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hn
  nlinarith [norm_nonneg (x-roundVec M x), Real.sqrt_nonneg (n:ℝ),
    mul_nonneg hδ (Real.sqrt_nonneg (n:ℝ))]

theorem section5_sgn_change_strip (a b : ℝ) (h : sgn a ≠ sgn b) : |a| ≤ |a-b| := by
  unfold sgn at h
  split_ifs at h with ha hb hb
  · exact False.elim (h rfl)
  · rw [abs_of_nonneg ha, abs_of_nonneg (by linarith : 0 ≤ a-b)]
    linarith
  · rw [abs_of_nonpos (by linarith : a ≤ 0), abs_of_nonpos (by linarith : a-b ≤ 0)]
    linarith
  · exact False.elim (h rfl)

theorem section5_rounding_label_strip {n M : ℕ} (hM : 1 ≤ M)
    (w x : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (h : ltf w 0 x ≠ ltf w 0 (roundVec M x)) :
    |inner ℝ w x| ≤ gridSpacing M * Real.sqrt n := by
  have hh : sgn (inner ℝ w x) ≠ sgn (inner ℝ w (roundVec M x)) := by
    simpa [ltf] using h
  have hs := section5_sgn_change_strip _ _ hh
  have hinner : |inner ℝ w x-inner ℝ w (roundVec M x)| ≤ ‖x-roundVec M x‖ := by
    rw [← inner_sub_right]
    simpa [hw] using norm_inner_le_norm (𝕜 := ℝ) w (x-roundVec M x)
  exact hs.trans (hinner.trans (section5_roundVec_error hM x))

theorem section5_gaussian_interval_bound (t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Set.Icc (-t) t) ≤ 2*t/(Real.sqrt (2*Real.pi)) := by
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    have hh : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    simpa using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹)
  have hi : IntegrableOn (gaussianPDFReal 0 1) (Set.Icc (-t) t) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hc : IntegrableOn (fun _ : ℝ => (Real.sqrt (2*Real.pi))⁻¹) (Set.Icc (-t) t) :=
    continuous_const.integrableOn_Icc
  change ((gaussianReal 0 1) (Set.Icc (-t) t)).toReal ≤ _
  rw [gaussianReal_apply_eq_integral 0 (by norm_num),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ x))]
  calc
    _ ≤ ∫ _ in Set.Icc (-t) t, (Real.sqrt (2*Real.pi))⁻¹ := integral_mono hi hc hpdf
    _ = _ := by
      simp only [setIntegral_const, Real.volume_real_Icc, smul_eq_mul]
      rw [max_eq_left (by linarith : 0 ≤ t- -t)]
      ring

theorem section5_gaussian_inner_strip {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | |inner ℝ w x| ≤ t} ≤
      2*t/Real.sqrt (2*Real.pi) := by
  let L := innerSL ℝ w
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    simp [L, innerSL_apply_norm, hw]
  have hevent : {x : EuclideanSpace ℝ (Fin n) | |inner ℝ w x| ≤ t} = L ⁻¹' Set.Icc (-t) t := by
    ext x
    simp [L, abs_le]
  change ((stdGaussian (EuclideanSpace ℝ (Fin n))) {x | |inner ℝ w x| ≤ t}).toReal ≤ _
  rw [hevent, ← Measure.map_apply L.continuous.measurable measurableSet_Icc, hmap]
  exact section5_gaussian_interval_bound t ht

theorem section5_rounding_constant {n M : ℕ} (hM : 1 ≤ M) :
    2*(gridSpacing M*Real.sqrt n)/Real.sqrt (2*Real.pi) = Real.sqrt (8*n/M) := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hδ : (gridSpacing M)^2 = 4*Real.pi/M := Real.sq_sqrt (by positivity)
  have hn : (Real.sqrt (n:ℝ))^2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hp : (Real.sqrt (2*Real.pi))^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hsq : (2*(gridSpacing M*Real.sqrt n)/Real.sqrt (2*Real.pi))^2 = 8*n/M := by
    rw [div_pow, mul_pow, mul_pow, hδ, hn, hp]
    field_simp
    ring
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 8*n/M by positivity)
  have hpos : 0 ≤ 2*(gridSpacing M*Real.sqrt n)/Real.sqrt (2*Real.pi) := by
    dsimp [gridSpacing]
    positivity
  nlinarith [Real.sqrt_nonneg (8*(n:ℝ)/M)]

theorem section5_discretization_measurable {n M : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x => (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2)) := by
  have hmround : Measurable (roundVec M : EuclideanSpace ℝ (Fin n) → _) := by
    unfold roundVec
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply measurable_pi_lambda
    intro i
    unfold roundCoord
    apply Measurable.add measurable_const
    apply Measurable.const_mul
    apply (measurable_of_countable (fun k : ℤ => (k:ℝ))).comp
    fun_prop
  have hltf : Measurable (ltf w 0) := by
    unfold ltf sgn
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_le measurable_const (by fun_prop)
  have hcast : Measurable (fun k : ℤ => (k:ℝ)) := measurable_of_countable _
  exact (hcast.comp (hltf.sub (hltf.comp hmround))).pow_const 2

theorem section5_discretization_integrable {n M : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply (integrable_const (4:ℝ)).mono' (section5_discretization_measurable w).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold ltf sgn
  split_ifs <;> norm_num

theorem section5_discretization_integral_bound {n M : ℕ} (hM : 1 ≤ M)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    ∫ x, (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ 4*Real.sqrt (8*n/M) := by
  classical
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | |inner ℝ w x| ≤ gridSpacing M*Real.sqrt n}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hf4 (x : EuclideanSpace ℝ (Fin n)) : f x ≤ 4 := by
    dsimp [f,ltf,sgn]
    split_ifs <;> norm_num
  have hfi : Integrable f μ := section5_discretization_integrable w
  have hind : Integrable (S.indicator (fun _ => (4:ℝ))) μ :=
    (integrable_const (4:ℝ)).indicator hS
  have hbound (x : EuclideanSpace ℝ (Fin n)) : f x ≤ S.indicator (fun _ => (4:ℝ)) x := by
    by_cases hs : x ∈ S
    · simpa [Set.indicator_of_mem hs] using hf4 x
    · have heq : ltf w 0 x = ltf w 0 (roundVec M x) := by
        by_contra h
        exact hs (section5_rounding_label_strip hM w x hw h)
      simp [f, heq, Set.indicator_of_notMem hs]
  change ∫ x, f x ∂μ ≤ _
  calc
    _ ≤ ∫ x, S.indicator (fun _ => (4:ℝ)) x ∂μ := integral_mono hfi hind hbound
    _ = 4*μ.real S := by rw [integral_indicator_const 4 hS]; simp [smul_eq_mul,mul_comm]
    _ ≤ 4*(2*(gridSpacing M*Real.sqrt n)/Real.sqrt (2*Real.pi)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact section5_gaussian_inner_strip w hw _ (by dsimp [gridSpacing]; positivity)
    _ = _ := by rw [section5_rounding_constant hM]

theorem solution : ∀ n M : ℕ, 1 ≤ n → 1 ≤ M →
    ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
    let L := gridRadius M
    ∫ x in {x : EuclideanSpace ℝ (Fin n) | ∀ i, -L ≤ x i ∧ x i ≤ L},
      (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ 4*Real.sqrt (8*n/M) := by
  intro n M hn hM w hw
  exact (setIntegral_le_integral (section5_discretization_integrable w)
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))).trans
      (section5_discretization_integral_bound hM w hw)
