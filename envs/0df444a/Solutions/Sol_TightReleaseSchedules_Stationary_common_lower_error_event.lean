-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.common_lower_error_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T17:07:28.172582+00:00
-- url     : https://prove2.me/submissions/824e151a-f1a3-4f66-9627-10c6bd33ff35

import Definitions.Def_TightReleaseSchedules_Stationary_multiscale_prior

section
/-!
PLAN (q382, Lemma 4.2). Constants: amp(l) = 2^{-5-l/2}, a = amp, rho = a sqrt|S|/16.
(1) per level ||level|| <= amp sqrt|S|; 2^{l0} >= 16|S|/Delta^2; geometric sum < Delta/32.
(2) core: change of measure.  Fix seed and the other levels (u0); the n observed rows depend on the
    level-l draw only through y_i = <x_i, theta0> + eps_i + <x_i, a u_l>.  Shear eps'_i = eps_i + <x_i,a u_l>
    (rows i<n) has density D = exp(sum eps' m_i - m_i^2/2) wrt gaussianRows.  P(success) = int D * Psi
    <= sqrt(int D^2) * sqrt(int Psi) (Cauchy-Schwarz).  int D^2 = (1-2|a u|^2)^{-n/2} <= exp(k 2^-10 * 1.001),
    int Psi <= 0.1293^k (Chernoff, lambda=128), (0.1293 * 1.0011)^{1/2} < 0.36 = 9/25.
(3) union bound over (slot, level) with estimator `if date <= n then head else 0`, n = min(T, floor 2^l);
    minimal l >= l0 with date <= 2^l, 2^l < 2 max(date, 16|S|/Delta^2).
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

namespace TRS.Dev.LowerErrorEventCube

lemma coord_integral (h : ℝ → ℝ) :
    ∫ t, h t.val ∂uniformCoordinate = (1 / 2 : ℝ) * ∫ t in Set.Icc (-1 : ℝ) 1, h t := by
  have hemb : MeasurableEmbedding (Subtype.val : CubeCoordinate → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  unfold uniformCoordinate
  rw [integral_smul_measure, ← hemb.integral_map, hemb.map_comap, Subtype.range_coe]
  simp [ENNReal.toReal_inv]

instance : IsProbabilityMeasure uniformCoordinate := by
  constructor
  have hemb : MeasurableEmbedding (Subtype.val : CubeCoordinate → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  unfold uniformCoordinate
  rw [Measure.smul_apply, hemb.comap_apply]
  simp
  have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := rfl
  rw [this, Real.volume_Icc]
  norm_num
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.inv_mul_cancel] <;> simp

lemma gauss_coord_integrable (l c : ℝ) (hl : 0 < l) :
    Integrable (fun t : CubeCoordinate => Real.exp (-l * (t.val - c) ^ 2)) uniformCoordinate := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (by fun_prop : Measurable fun t : CubeCoordinate => Real.exp (-l * (t.val - c) ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (t.val - c)]

lemma gauss_coord (l c : ℝ) (hl : 0 < l) :
    ∫ t, Real.exp (-l * (t.val - c) ^ 2) ∂uniformCoordinate ≤ (1 / 2 : ℝ) * Real.sqrt (Real.pi / l) := by
  rw [coord_integral (fun t => Real.exp (-l * (t - c) ^ 2))]
  have h1 : ∫ t in Set.Icc (-1 : ℝ) 1, Real.exp (-l * (t - c) ^ 2) ≤
      ∫ t, Real.exp (-l * (t - c) ^ 2) := by
    apply setIntegral_le_integral
    · have := integrable_exp_neg_mul_sq hl
      simpa [neg_mul] using this.comp_sub_right c
    · exact Filter.Eventually.of_forall fun t => (Real.exp_pos _).le
  have h2 : ∫ t : ℝ, Real.exp (-l * (t - c) ^ 2) = Real.sqrt (Real.pi / l) := by
    rw [integral_sub_right_eq_self (fun t => Real.exp (-l * t ^ 2)) c]
    exact integral_gaussian l
  nlinarith [h1, h2]

lemma cube_chernoff {ι : Type} [Fintype ι] (c : ι → ℝ) (r l : ℝ) (hl : 0 < l) :
    (Measure.pi (fun _ : ι => uniformCoordinate)).real
      {u : ι → CubeCoordinate | ∑ i, ((u i).val - c i) ^ 2 ≤ r} ≤
      Real.exp (l * r) * ((1 / 2 : ℝ) * Real.sqrt (Real.pi / l)) ^ Fintype.card ι := by
  set μ : Measure (ι → CubeCoordinate) := Measure.pi (fun _ : ι => uniformCoordinate)
  have hprod : ∫ u, ∏ i, Real.exp (-l * ((u i).val - c i) ^ 2) ∂μ ≤
      ((1 / 2 : ℝ) * Real.sqrt (Real.pi / l)) ^ Fintype.card ι := by
    rw [integral_fintype_prod_eq_prod (fun i (t : CubeCoordinate) =>
      Real.exp (-l * (t.val - c i) ^ 2))]
    calc ∏ i, ∫ t, Real.exp (-l * (t.val - c i) ^ 2) ∂uniformCoordinate
        ≤ ∏ _i : ι, ((1 / 2 : ℝ) * Real.sqrt (Real.pi / l)) := by
          apply Finset.prod_le_prod
          · intro i _; exact integral_nonneg fun t => (Real.exp_pos _).le
          · intro i _; exact gauss_coord l (c i) hl
      _ = _ := by simp
  have hint : Integrable (fun u : ι → CubeCoordinate =>
      ∏ i, Real.exp (-l * ((u i).val - c i) ^ 2)) μ :=
    Integrable.fintype_prod (f := fun i (t : CubeCoordinate) => Real.exp (-l * (t.val - c i) ^ 2))
      (fun i => gauss_coord_integrable l (c i) hl)
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun u => ∏ i, Real.exp (-l * ((u i).val - c i) ^ 2))
    (Filter.Eventually.of_forall fun u => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
    hint (Real.exp (-l * r))
  have hsub : {u : ι → CubeCoordinate | ∑ i, ((u i).val - c i) ^ 2 ≤ r} ⊆
      {u | Real.exp (-l * r) ≤ ∏ i, Real.exp (-l * ((u i).val - c i) ^ 2)} := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    rw [← Finset.mul_sum]
    nlinarith
  have h3 := measureReal_mono (μ := μ) hsub (by simp)
  have h4 : Real.exp (-l * r) * μ.real {u : ι → CubeCoordinate | ∑ i, ((u i).val - c i) ^ 2 ≤ r}
      ≤ ((1 / 2 : ℝ) * Real.sqrt (Real.pi / l)) ^ Fintype.card ι := by
    calc _ ≤ Real.exp (-l * r) * μ.real _ := by
          gcongr
      _ ≤ _ := hmark
      _ ≤ _ := hprod
  have hpos := Real.exp_pos (l * r)
  have : Real.exp (l * r) * Real.exp (-l * r) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [measureReal_nonneg (μ := μ) (s := {u : ι → CubeCoordinate | ∑ i, ((u i).val - c i) ^ 2 ≤ r})]

lemma chernoff_const : Real.exp (1 / 2) * ((1 / 2 : ℝ) * Real.sqrt (Real.pi / 128)) ≤ 1293 / 10000 := by
  have he : Real.exp (1 / 2) ≤ 16488 / 10000 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2)]
  have hs : Real.sqrt (Real.pi / 128) ≤ 1567 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d4]
  have := Real.exp_pos (1 / 2)
  nlinarith [Real.sqrt_nonneg (Real.pi / 128)]

/-- Chernoff bound: a ball of radius `sqrt k / 16` (in the rescaled cube) has uniform mass `<= 0.1293^k`. -/
lemma cube_ball {ι : Type} [Fintype ι] (c : ι → ℝ) :
    (Measure.pi (fun _ : ι => uniformCoordinate)).real
      {u : ι → CubeCoordinate | ∑ i, ((u i).val - c i) ^ 2 ≤ (Fintype.card ι : ℝ) / 256} ≤
      (1293 / 10000 : ℝ) ^ Fintype.card ι := by
  refine (cube_chernoff c _ 128 (by norm_num)).trans ?_
  have : Real.exp (128 * ((Fintype.card ι : ℝ) / 256)) = Real.exp (1 / 2) ^ Fintype.card ι := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [this, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) chernoff_const _

end TRS.Dev.LowerErrorEventCube
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventLevels

lemma amp_sq (ℓ : ℤ) : levelAmplitude ℓ ^ 2 = (2 : ℝ) ^ (-10 : ℤ) * (2 : ℝ) ^ (-ℓ) := by
  unfold levelAmplitude
  rw [Real.sq_sqrt (by positivity)]

lemma amp_pos (ℓ : ℤ) : 0 < levelAmplitude ℓ := by
  unfold levelAmplitude; positivity

lemma amp_succ (ℓ : ℤ) : levelAmplitude (ℓ + 1) = levelAmplitude ℓ * Real.sqrt (1 / 2) := by
  unfold levelAmplitude
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [neg_add, zpow_add₀ (by norm_num)]
  simp; ring

lemma amp_add_nat (ℓ : ℤ) (j : ℕ) :
    levelAmplitude (ℓ + j) = levelAmplitude ℓ * Real.sqrt (1 / 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.cast_succ, ← add_assoc, amp_succ, ih]; ring

lemma sqrt_half_lt : Real.sqrt (1 / 2) < 5 / 7 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sum_amp (a L : ℤ) (h : a ≤ L) :
    ∑ ℓ ∈ Finset.Icc a L, levelAmplitude ℓ ≤ levelAmplitude a * (7 / 2) := by
  have hN : Finset.Icc a L = (Finset.range (L - a + 1).toNat).image (fun j : ℕ => a + (j : ℤ)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      refine ⟨(x - a).toNat, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hN, Finset.sum_image (fun x _ y _ hxy => by simpa using hxy)]
  simp_rw [amp_add_nat, ← Finset.mul_sum]
  have hr0 : 0 ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
  have hr := sqrt_half_lt
  have hgeom : ∑ j ∈ Finset.range (L - a + 1).toNat, Real.sqrt (1 / 2) ^ j ≤ 7 / 2 := by
    rw [geom_sum_eq (by linarith)]
    have : Real.sqrt (1 / 2) ^ (L - a + 1).toNat ≥ 0 := by positivity
    rw [div_le_iff_of_neg (by linarith)]
    nlinarith
  nlinarith [amp_pos a]

lemma two_zpow_firstLevel_ge (k : ℕ) (Δ : ℝ) (hk : 0 < k) (hΔ : 0 < Δ) (ℓ : ℤ)
    (hℓ : firstLevel k Δ ≤ ℓ) : 16 * (k : ℝ) / Δ ^ 2 ≤ (2 : ℝ) ^ ℓ := by
  have hx : 0 < 16 * (k : ℝ) / Δ ^ 2 := by positivity
  have h1 : logTwo (16 * (k : ℝ) / Δ ^ 2) ≤ (firstLevel k Δ : ℝ) := Int.le_ceil _
  have h2 : (2 : ℝ) ^ (logTwo (16 * (k : ℝ) / Δ ^ 2)) = 16 * (k : ℝ) / Δ ^ 2 := by
    unfold logTwo
    rw [← Real.logb]
    exact Real.rpow_logb (by norm_num) (by norm_num) hx
  calc 16 * (k : ℝ) / Δ ^ 2 = (2 : ℝ) ^ (logTwo (16 * (k : ℝ) / Δ ^ 2)) := h2.symm
    _ ≤ (2 : ℝ) ^ (ℓ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (h1.trans (by exact_mod_cast hℓ))
    _ = (2 : ℝ) ^ ℓ := Real.rpow_intCast _ _

lemma two_zpow_firstLevel_lt (k : ℕ) (Δ : ℝ) (hk : 0 < k) (hΔ : 0 < Δ) :
    (2 : ℝ) ^ (firstLevel k Δ) < 2 * (16 * (k : ℝ) / Δ ^ 2) := by
  have hx : 0 < 16 * (k : ℝ) / Δ ^ 2 := by positivity
  have h1 : (firstLevel k Δ : ℝ) < logTwo (16 * (k : ℝ) / Δ ^ 2) + 1 := Int.ceil_lt_add_one _
  have h2 : (2 : ℝ) ^ (logTwo (16 * (k : ℝ) / Δ ^ 2)) = 16 * (k : ℝ) / Δ ^ 2 := by
    unfold logTwo
    rw [← Real.logb]
    exact Real.rpow_logb (by norm_num) (by norm_num) hx
  calc (2 : ℝ) ^ (firstLevel k Δ) = (2 : ℝ) ^ ((firstLevel k Δ : ℤ) : ℝ) := (Real.rpow_intCast _ _).symm
    _ < (2 : ℝ) ^ (logTwo (16 * (k : ℝ) / Δ ^ 2) + 1) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
    _ = 2 * (16 * (k : ℝ) / Δ ^ 2) := by rw [Real.rpow_add (by norm_num), h2]; simp; ring

lemma vec_norm_le {d : ℕ} (S : Finset (Fin d)) (v : S → CubeCoordinate) :
    ‖(WithLp.toLp 2 (fun i : S => (v i : ℝ)) : BlockVector S)‖ ≤ Real.sqrt S.card := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i : S, ‖(v i : ℝ)‖ ^ 2 ≤ ∑ _i : S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have := (v i).2
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [this.1, this.2]
    _ = S.card := by simp

lemma part1 {d : ℕ} (S : Finset (Fin d)) (hS : 0 < S.card) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1)
    (L : ℤ) (hL : firstLevel S.card Δ ≤ L) (u : PriorDraws S Δ L) :
    ‖hiddenShift S Δ L u‖ < Δ / 32 := by
  set k := S.card
  have hk : (0 : ℝ) < k := by exact_mod_cast hS
  unfold hiddenShift
  calc ‖∑ ℓ, levelAmplitude ℓ.val • (WithLp.toLp 2 (fun i : S => (u ℓ i : ℝ)) : BlockVector S)‖
      ≤ ∑ ℓ, ‖levelAmplitude ℓ.val • (WithLp.toLp 2 (fun i : S => (u ℓ i : ℝ)) : BlockVector S)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ℓ : ↥(Finset.Icc (firstLevel k Δ) L), levelAmplitude ℓ.val * Real.sqrt k := by
        apply Finset.sum_le_sum
        intro ℓ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (amp_pos _)]
        exact mul_le_mul_of_nonneg_left (vec_norm_le S _) (amp_pos _).le
    _ = (∑ ℓ ∈ Finset.Icc (firstLevel k Δ) L, levelAmplitude ℓ) * Real.sqrt k := by
        rw [← Finset.sum_mul, ← Finset.sum_coe_sort (Finset.Icc (firstLevel k Δ) L)]
    _ ≤ (levelAmplitude (firstLevel k Δ) * (7 / 2)) * Real.sqrt k := by
        gcongr
        exact sum_amp _ _ hL
    _ < Δ / 32 := by
        have h2 := two_zpow_firstLevel_ge k Δ hS hΔ (firstLevel k Δ) le_rfl
        have h3 : levelAmplitude (firstLevel k Δ) ^ 2 * k ≤ (Δ / 128) ^ 2 := by
          rw [amp_sq, zpow_neg (2 : ℝ) (firstLevel k Δ)]
          have hp : (0 : ℝ) < (2 : ℝ) ^ (firstLevel k Δ) := by positivity
          rw [show ((2 : ℝ) ^ (-10 : ℤ)) = 1 / 1024 by norm_num]
          rw [div_le_iff₀ (by positivity)] at h2
          rw [show (Δ / 128) ^ 2 = Δ ^ 2 / 16384 by ring]
          have : ((2 : ℝ) ^ (firstLevel k Δ))⁻¹ * k ≤ Δ ^ 2 / 16 := by
            rw [inv_mul_le_iff₀ hp]; nlinarith
          nlinarith
        have h4 : levelAmplitude (firstLevel k Δ) * Real.sqrt k ≤ Δ / 128 := by
          apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
          rw [mul_pow, Real.sq_sqrt hk.le]; exact h3
        nlinarith

end TRS.Dev.LowerErrorEventLevels

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventShear

lemma pdf_shift (m ε : ℝ) :
    gaussianPDF m 1 ε = gaussianPDF 0 1 ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) := by
  unfold gaussianPDF gaussianPDFReal
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_one, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gauss_shift_lintegral (m : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ε, F (ε + m) ∂(gaussianReal 0 1) =
      ∫⁻ ε, F ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ∂(gaussianReal 0 1) := by
  have h1 : ∫⁻ ε, F (ε + m) ∂(gaussianReal 0 1) = ∫⁻ ε, F ε ∂(gaussianReal m 1) := by
    have := gaussianReal_map_add_const (μ := 0) (v := 1) m
    rw [zero_add] at this
    rw [← this, lintegral_map hF (measurable_add_const m)]
  rw [h1, gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hF,
    lintegral_withDensity_eq_lintegral_mul (g := fun ε => F ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)))
      _ (measurable_gaussianPDF _ _) (hF.mul (by fun_prop))]
  refine lintegral_congr fun ε => ?_
  simp only [Pi.mul_apply]
  rw [pdf_shift]; ring

abbrev Row (d : ℕ) := Vector d × ℝ

def rowMeasure (d : ℕ) : Measure (Row d) := (stdGaussian (Vector d)).prod (gaussianReal 0 1)

instance (d : ℕ) : IsProbabilityMeasure (rowMeasure d) := by
  unfold rowMeasure; infer_instance

def rowShear {d : ℕ} (e : Vector d) (r : Row d) : Row d := (r.1, r.2 + inner ℝ r.1 e)

def rowD {d : ℕ} (e : Vector d) (r : Row d) : ℝ :=
  Real.exp (r.2 * inner ℝ r.1 e - (inner ℝ r.1 e) ^ 2 / 2)

lemma measurable_rowShear {d : ℕ} (e : Vector d) : Measurable (rowShear e) := by
  unfold rowShear; fun_prop

lemma measurable_rowD {d : ℕ} (e : Vector d) : Measurable (rowD e) := by
  unfold rowD; fun_prop

lemma row_shear_lintegral {d : ℕ} (e : Vector d) (F : Row d → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ r, F (rowShear e r) ∂(rowMeasure d) =
      ∫⁻ r, F r * ENNReal.ofReal (rowD e r) ∂(rowMeasure d) := by
  unfold rowMeasure
  rw [lintegral_prod (fun r : Row d => F (rowShear e r)) ((hF.comp (measurable_rowShear e)).aemeasurable),
    lintegral_prod (fun r : Row d => F r * ENNReal.ofReal (rowD e r))
      ((hF.mul (measurable_rowD e).ennreal_ofReal).aemeasurable)]
  refine lintegral_congr fun x => ?_
  have := gauss_shift_lintegral (inner ℝ x e) (fun ε => F (x, ε)) (hF.comp measurable_prodMk_left)
  simpa [rowShear, rowD] using this

lemma row_shear_map {d : ℕ} (e : Vector d) :
    (rowMeasure d).map (rowShear e) =
      (rowMeasure d).withDensity (fun r => ENNReal.ofReal (rowD e r)) := by
  ext s hs
  rw [Measure.map_apply (measurable_rowShear e) hs, withDensity_apply _ hs,
    ← lintegral_indicator hs, ← lintegral_indicator_one (measurable_rowShear e hs)]
  have := row_shear_lintegral e (s.indicator 1) (measurable_one.indicator hs)
  have h2 : ∫⁻ a, (rowShear e ⁻¹' s).indicator 1 a ∂rowMeasure d =
      ∫⁻ r, s.indicator 1 (rowShear e r) ∂rowMeasure d := by
    refine lintegral_congr fun r => ?_
    by_cases h : rowShear e r ∈ s <;> simp [h, Set.indicator]
  rw [h2, this]
  refine lintegral_congr fun r => ?_
  by_cases h : r ∈ s <;> simp [h, Set.indicator]

lemma gauss_exp_sq (σ2 : ℝ≥0) (h : 2 * (σ2 : ℝ) < 1) :
    ∫ t, Real.exp (t ^ 2) ∂(gaussianReal 0 σ2) = 1 / Real.sqrt (1 - 2 * σ2) := by
  by_cases h0 : σ2 = 0
  · subst h0; simp [gaussianReal_zero_var]
  have hpos : (0 : ℝ) < σ2 := by positivity
  rw [integral_gaussianReal_eq_integral_smul h0]
  have hb : (0 : ℝ) < 1 / (2 * σ2) - 1 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have : ∀ x : ℝ, gaussianPDFReal 0 σ2 x • Real.exp (x ^ 2) =
      (Real.sqrt (2 * Real.pi * σ2))⁻¹ * Real.exp (-(1 / (2 * σ2) - 1) * x ^ 2) := by
    intro x
    unfold gaussianPDFReal
    rw [smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [this]
  rw [integral_const_mul, integral_gaussian]
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), one_div]
  congr 1
  field_simp
  have h1 : (1 - (σ2 : ℝ) * 2) ≠ 0 := by linarith
  ring_nf
  first | rfl | (rw [Real.sqrt_inv]) 

lemma eps_sq_lintegral (m : ℝ) :
    ∫⁻ ε, ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ^ 2 ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (m ^ 2)) := by
  have hint : Integrable (fun ε : ℝ => Real.exp (-(m ^ 2)) * Real.exp ((2 * m) * ε))
      (gaussianReal 0 1) := (integrable_exp_mul_gaussianReal (2 * m)).const_mul _
  have h1 : ∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ^ 2 =
      ENNReal.ofReal (Real.exp (-(m ^ 2)) * Real.exp ((2 * m) * ε)) := by
    intro ε
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ε =>
    by positivity), integral_const_mul]
  congr 1
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (2 * m)
  simp only [mgf, id] at this
  rw [this, ← Real.exp_add]
  congr 1
  simp; ring

lemma stdGaussian_inner_exp_sq {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫ x, Real.exp (inner ℝ x e ^ 2) ∂(stdGaussian (Vector d)) = 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
  set L : StrongDual ℝ (Vector d) := innerSL ℝ e
  have hL : ∀ x, L x = inner ℝ x e := fun x => by simp [L, real_inner_comm]
  have hmap := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (Vector d)) L
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian] at hmap
  have hn : ‖L‖ = ‖e‖ := by simp [L]
  rw [hn] at hmap
  have hnn : ((‖e‖ ^ 2).toNNReal : ℝ) = ‖e‖ ^ 2 := Real.coe_toNNReal _ (by positivity)
  have := gauss_exp_sq (‖e‖ ^ 2).toNNReal (by rw [hnn]; exact h)
  rw [hnn] at this
  rw [← this, ← hmap, integral_map L.continuous.aemeasurable (by fun_prop)]
  simp [hL]

end TRS.Dev.LowerErrorEventShear

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventShearPi

lemma pi_withDensity {ι : Type} [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hint : ∀ i, Integrable (f i) ν) :
    (Measure.pi (fun _ : ι => ν)).withDensity (fun z => ENNReal.ofReal (∏ i, f i (z i))) =
      Measure.pi (fun i => ν.withDensity (fun x => ENNReal.ofReal (f i x))) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  have h1 : ∀ z : ι → X, (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (∏ i, f i (z i))) z =
      ENNReal.ofReal (∏ i, (s i).indicator (f i) (z i)) := by
    intro z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz]
      have : ∏ i, f i (z i) = ∏ i, (s i).indicator (f i) (z i) :=
        Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hz i (Set.mem_univ i)) _).symm
      rw [this]
    · rw [Set.indicator_of_notMem hz]
      have : ∃ i, z i ∉ s i := by
        by_contra hc
        push Not at hc
        exact hz fun i _ => hc i
      obtain ⟨i, hi⟩ := this
      have : ∏ i, (s i).indicator (f i) (z i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [this]; simp
  rw [← lintegral_indicator hbox]
  simp_rw [h1]
  have hint2 : ∀ i, Integrable ((s i).indicator (f i)) ν := fun i => (hint i).indicator (hs i)
  have hnn2 : ∀ i x, 0 ≤ (s i).indicator (f i) x := fun i x =>
    Set.indicator_nonneg (fun y _ => hnn i y) x
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (f := fun i x => (s i).indicator (f i) x) hint2)
    (Filter.Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => hnn2 i _),
    integral_fintype_prod_eq_prod (fun i x => (s i).indicator (f i) x),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn2 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), integral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hint i).restrict
    (Filter.Eventually.of_forall fun x => hnn i x)]

open TRS.Dev.LowerErrorEventShear

lemma rowD_lintegral {d : ℕ} (e : Vector d) :
    ∫⁻ r, ENNReal.ofReal (rowD e r) ∂(rowMeasure d) = 1 := by
  have := congrArg (fun m => m Set.univ) (row_shear_map e)
  simp only [Measure.map_apply (measurable_rowShear e) MeasurableSet.univ, Set.preimage_univ,
    measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  exact this.symm

lemma rowD_integrable {d : ℕ} (e : Vector d) : Integrable (rowD e) (rowMeasure d) := by
  refine ⟨(measurable_rowD e).aestronglyMeasurable, ?_⟩
  have h : ∀ r, ‖rowD e r‖ₑ = ENNReal.ofReal (rowD e r) := fun r => by
    rw [Real.enorm_eq_ofReal (show 0 ≤ rowD e r from (Real.exp_pos _).le)]
  simp only [HasFiniteIntegral, h, rowD_lintegral]
  exact ENNReal.one_lt_top

def rowF {T d : ℕ} (n : ℕ) (e : Vector d) (i : Fin T) : Row d → ℝ :=
  if i.val < n then rowD e else fun _ => 1

def rowG {T d : ℕ} (n : ℕ) (e : Vector d) (i : Fin T) : Row d → Row d :=
  if i.val < n then rowShear e else id

def shearAll {T d : ℕ} (n : ℕ) (e : Vector d) (z : GaussianRows T d) : GaussianRows T d :=
  fun i => rowG n e i (z i)

def densityAll {T d : ℕ} (n : ℕ) (e : Vector d) (z : GaussianRows T d) : ℝ :=
  ∏ i, rowF n e i (z i)

lemma measurable_rowG {T d : ℕ} (n : ℕ) (e : Vector d) (i : Fin T) : Measurable (rowG n e i) := by
  unfold rowG; split_ifs
  · exact measurable_rowShear e
  · exact measurable_id

lemma measurable_rowF {T d : ℕ} (n : ℕ) (e : Vector d) (i : Fin T) : Measurable (rowF n e i) := by
  unfold rowF; split_ifs
  · exact measurable_rowD e
  · exact measurable_const

lemma measurable_shearAll {T d : ℕ} (n : ℕ) (e : Vector d) :
    Measurable (shearAll (T := T) n e) :=
  measurable_pi_lambda _ fun i => (measurable_rowG n e i).comp (measurable_pi_apply i)

lemma measurable_densityAll {T d : ℕ} (n : ℕ) (e : Vector d) :
    Measurable (densityAll (T := T) n e) :=
  Finset.measurable_prod _ fun i _ => (measurable_rowF n e i).comp (measurable_pi_apply i)

lemma rowF_nonneg {T d : ℕ} (n : ℕ) (e : Vector d) (i : Fin T) (r : Row d) : 0 ≤ rowF n e i r := by
  unfold rowF; split_ifs
  · exact (Real.exp_pos _).le
  · exact zero_le_one

lemma rowF_integrable {T d : ℕ} (n : ℕ) (e : Vector d) (i : Fin T) :
    Integrable (rowF n e i) (rowMeasure d) := by
  unfold rowF; split_ifs
  · exact rowD_integrable e
  · exact integrable_const _

lemma map_rowG {T d : ℕ} (n : ℕ) (e : Vector d) (i : Fin T) :
    (rowMeasure d).map (rowG n e i) =
      (rowMeasure d).withDensity (fun r => ENNReal.ofReal (rowF n e i r)) := by
  unfold rowG rowF; split_ifs
  · exact row_shear_map e
  · simp

lemma shear_map {T d : ℕ} (n : ℕ) (e : Vector d) :
    (gaussianRows T d).map (shearAll n e) =
      (gaussianRows T d).withDensity (fun z => ENNReal.ofReal (densityAll n e z)) := by
  unfold gaussianRows
  have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
  rw [h1]
  have h2 : shearAll (T := T) n e = fun z i => rowG n e i (z i) := rfl
  rw [h2]
  have : ∀ i : Fin T, SigmaFinite ((rowMeasure d).map (rowG n e i)) := fun i => inferInstance
  rw [Measure.pi_map_pi (fun i => (measurable_rowG n e i).aemeasurable)]
  unfold densityAll
  rw [pi_withDensity (rowMeasure d) (fun i => rowF n e i) (fun i => measurable_rowF n e i)
    (fun i r => rowF_nonneg n e i r) (fun i => rowF_integrable n e i)]
  congr 1
  funext i
  exact map_rowG n e i

lemma shear_lintegral {T d : ℕ} (n : ℕ) (e : Vector d) (F : GaussianRows T d → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F (shearAll n e z) ∂(gaussianRows T d) =
      ∫⁻ z, ENNReal.ofReal (densityAll n e z) * F z ∂(gaussianRows T d) := by
  rw [← lintegral_map hF (measurable_shearAll n e), shear_map,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_densityAll n e).ennreal_ofReal hF]
  rfl

lemma rowD_sq_lintegral {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫⁻ r, ENNReal.ofReal (rowD e r ^ 2) ∂(rowMeasure d) =
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2)) := by
  have hpos : 0 < 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
    have : 0 < 1 - 2 * ‖e‖ ^ 2 := by linarith
    positivity
  have hint : Integrable (fun x : Vector d => Real.exp (inner ℝ x e ^ 2)) (stdGaussian (Vector d)) := by
    apply Integrable.of_integral_ne_zero
    rw [stdGaussian_inner_exp_sq e h]; exact hpos.ne'
  unfold rowMeasure
  rw [lintegral_prod (fun r : Row d => ENNReal.ofReal (rowD e r ^ 2))
    (((measurable_rowD e).pow_const 2).ennreal_ofReal.aemeasurable)]
  have h1 : ∀ x : Vector d, ∫⁻ ε, ENNReal.ofReal (rowD e (x, ε) ^ 2) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (inner ℝ x e ^ 2)) := by
    intro x
    rw [← eps_sq_lintegral (inner ℝ x e)]
    refine lintegral_congr fun ε => ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    rfl
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
    (Real.exp_pos _).le), stdGaussian_inner_exp_sq e h]

lemma rowD_sq_integrable {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    Integrable (fun r => rowD e r ^ 2) (rowMeasure d) := by
  refine ⟨((measurable_rowD e).pow_const 2).aestronglyMeasurable, ?_⟩
  have h1 : ∀ r, ‖rowD e r ^ 2‖ₑ = ENNReal.ofReal (rowD e r ^ 2) := fun r => by
    rw [Real.enorm_eq_ofReal (show 0 ≤ rowD e r ^ 2 by positivity)]
  simp only [HasFiniteIntegral, h1, rowD_sq_lintegral e h]
  exact ENNReal.ofReal_lt_top

lemma rowD_sq_integral {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫ r, rowD e r ^ 2 ∂(rowMeasure d) = 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
  have hpos : 0 < 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
    have : 0 < 1 - 2 * ‖e‖ ^ 2 := by linarith
    positivity
  have := rowD_sq_lintegral e h
  rw [← ofReal_integral_eq_lintegral_ofReal (rowD_sq_integrable e h)
    (Filter.Eventually.of_forall fun r => by positivity)] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun r => by positivity) hpos.le).1 this

/-- Second moment of the density of the `n`-row shear. -/
lemma densityAll_sq_integral {T d : ℕ} (n : ℕ) (hn : n ≤ T) (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫ z, densityAll n e z ^ 2 ∂(gaussianRows T d) = (1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2)) ^ n := by
  unfold densityAll gaussianRows
  have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
  rw [h1]
  simp_rw [← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (fun i (r : Row d) => rowF n e i r ^ 2)]
  have : ∀ i : Fin T, ∫ r, rowF n e i r ^ 2 ∂(rowMeasure d) =
      if i.val < n then 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) else 1 := by
    intro i
    unfold rowF
    split_ifs
    · exact rowD_sq_integral e h
    · simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter fun i : Fin T => i.val < n) = Finset.univ.image (Fin.castLE hn) := by
    ext i; simp
    constructor
    · intro hi; exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩; exact j.2
  rw [this, Finset.card_image_of_injective _ (Fin.castLE_injective hn)]
  simp

lemma densityAll_sq_lintegral {T d : ℕ} (n : ℕ) (hn : n ≤ T) (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫⁻ z, ENNReal.ofReal (densityAll n e z) ^ 2 ∂(gaussianRows T d) =
      ENNReal.ofReal ((1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2)) ^ n) := by
  have hint : Integrable (fun z : GaussianRows T d => densityAll n e z ^ 2) (gaussianRows T d) := by
    unfold densityAll gaussianRows
    have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
        Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
    rw [h1]
    simp_rw [← Finset.prod_pow]
    refine Integrable.fintype_prod (f := fun i (r : Row d) => rowF n e i r ^ 2) fun i => ?_
    unfold rowF
    split_ifs
    · exact rowD_sq_integrable e h
    · simpa using integrable_const (1 : ℝ)
  rw [← densityAll_sq_integral n hn e h]
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => by positivity)]
  refine lintegral_congr fun z => ?_
  exact (ENNReal.ofReal_pow (Finset.prod_nonneg fun i _ => rowF_nonneg n e i (z i)) 2).symm

end TRS.Dev.LowerErrorEventShearPi

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventCore1

lemma embedBlock_add {d : ℕ} (S : Finset (Fin d)) (v w : BlockVector S) :
    embedBlock S (v + w) = embedBlock S v + embedBlock S w := by
  ext i
  unfold embedBlock
  by_cases h : i ∈ S <;> simp [h]

lemma norm_embedBlock {d : ℕ} (S : Finset (Fin d)) (v : BlockVector S) :
    ‖embedBlock S v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  set F : Fin d → ℝ := fun i => ‖(if h : i ∈ S then v ⟨i, h⟩ else 0 : ℝ)‖ ^ 2 with hF
  have h1 : ∑ i : Fin d, ‖(embedBlock S v) i‖ ^ 2 = ∑ i : Fin d, F i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [embedBlock, hF]
  have h2 : ∑ i : S, ‖v i‖ ^ 2 = ∑ i ∈ S, F i := by
    rw [← Finset.sum_coe_sort S F]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hF]
  rw [h1, h2]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp [hF, hi]

def vecOf {d : ℕ} {S : Finset (Fin d)} (v : S → CubeCoordinate) : BlockVector S :=
  WithLp.toLp 2 (fun i : S => (v i : ℝ))

def zeroC : CubeCoordinate := ⟨0, by norm_num⟩

lemma hiddenShift_update {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (u : PriorDraws S Δ L) :
    hiddenShift S Δ L u = hiddenShift S Δ L (Function.update u ℓ' (fun _ => zeroC)) +
      levelAmplitude ℓ'.val • vecOf (u ℓ') := by
  unfold hiddenShift
  have key : ∀ ℓ : ↥(Finset.Icc (firstLevel S.card Δ) L),
      levelAmplitude ℓ.val • WithLp.toLp 2 (fun i : S => (u ℓ i : ℝ)) =
      levelAmplitude ℓ.val • WithLp.toLp 2 (fun i : S => (Function.update u ℓ' (fun _ => zeroC) ℓ i : ℝ))
        + (if ℓ = ℓ' then levelAmplitude ℓ'.val • vecOf (u ℓ') else 0) := by
    intro ℓ
    by_cases h : ℓ = ℓ'
    · subst h
      simp only [Function.update_self, if_true]
      ext i
      simp [zeroC, vecOf]
    · simp [h, Function.update_of_ne h]
  rw [Finset.sum_congr rfl fun ℓ _ => key ℓ, Finset.sum_add_distrib]
  simp

lemma measurable_vecOf {d : ℕ} {S : Finset (Fin d)} : Measurable (vecOf (S := S)) := by
  unfold vecOf
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

lemma measurable_hiddenShift {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    Measurable (hiddenShift S Δ L) := by
  unfold hiddenShift
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  have : Measurable fun u : PriorDraws S Δ L => vecOf (u ℓ) :=
    measurable_vecOf.comp (measurable_pi_apply ℓ)
  exact this.const_smul (levelAmplitude ℓ.val)

lemma measurable_embedBlock {d : ℕ} (S : Finset (Fin d)) : Measurable (embedBlock S) := by
  unfold embedBlock
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ S
  · simp only [h, dif_pos]
    exact (measurable_pi_apply (⟨i, h⟩ : S)).comp (PiLp.continuous_ofLp 2 _).measurable
  · simp [h]

lemma measurable_priorTranscript {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) : Measurable (priorTranscript (s := s) (S := S) (Δ := Δ) (L := L) g) := by
  unfold priorTranscript observations
  refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
  have hθ : Measurable fun ω : PriorSample s T d S Δ L =>
      g i + embedBlock S (hiddenShift S Δ L ω.2.1) :=
    measurable_const.add ((measurable_embedBlock S).comp
      ((measurable_hiddenShift S Δ L).comp (measurable_fst.comp measurable_snd)))
  have hx : Measurable fun ω : PriorSample s T d S Δ L => (ω.2.2 i).1 :=
    measurable_fst.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
  have he : Measurable fun ω : PriorSample s T d S Δ L => (ω.2.2 i).2 :=
    measurable_snd.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
  exact hx.prodMk ((hx.inner hθ).add he)

lemma priorInformation_le {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (n : ℕ) :
    priorInformation (s := s) (S := S) (Δ := Δ) (L := L) g n ≤
      (inferInstance : MeasurableSpace (PriorSample s T d S Δ L)) := by
  have hF : Measurable (fun ω : Transcript s T d =>
      (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) := by
    refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
    by_cases h : i.val < n
    · simp only [h, if_true]
      exact (measurable_pi_apply i).comp measurable_snd
    · simp [h]
  have hI : information s T d n ≤ (inferInstance : MeasurableSpace (Transcript s T d)) :=
    hF.comap_le
  calc priorInformation (s := s) (S := S) (Δ := Δ) (L := L) g n
      ≤ MeasurableSpace.comap (priorTranscript g) inferInstance :=
        MeasurableSpace.comap_mono hI
    _ ≤ _ := (measurable_priorTranscript g).comap_le

lemma est_factor {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (n : ℕ) (ŵ : PriorSample s T d S Δ L → Vector d)
    (hŵ : @Measurable _ _ (priorInformation g n) inferInstance ŵ)
    (ω ω' : PriorSample s T d S Δ L)
    (h1 : (priorTranscript g ω).1 = (priorTranscript g ω').1)
    (h2 : ∀ i : Fin T, i.val < n → (priorTranscript g ω).2 i = (priorTranscript g ω').2 i) :
    ŵ ω = ŵ ω' := by
  have ht : MeasurableSet ({ŵ ω} : Set (Vector d)) := measurableSet_singleton _
  have h := hŵ ht
  unfold priorInformation information at h
  rw [MeasurableSpace.measurableSet_comap] at h
  obtain ⟨B1, hB1, hB1e⟩ := h
  rw [MeasurableSpace.measurableSet_comap] at hB1
  obtain ⟨B2, hB2, hB2e⟩ := hB1
  have hF : (fun ω : Transcript s T d => (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0)))
        (priorTranscript g ω) =
      (fun ω : Transcript s T d => (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0)))
        (priorTranscript g ω') := by
    refine Prod.ext h1 (funext fun i => ?_)
    by_cases hi : i.val < n
    · simp [hi, h2 i hi]
    · simp [hi]
  have hmem : ω ∈ priorTranscript g ⁻¹' B1 := by
    rw [hB1e]; simp
  rw [← hB2e] at hmem
  have hmem' : ω' ∈ priorTranscript g ⁻¹' B1 := by
    rw [← hB2e]
    have a : (fun ω : Transcript s T d => (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0)))
        (priorTranscript g ω) ∈ B2 := hmem
    rw [hF] at a
    exact a
  rw [hB1e] at hmem'
  simpa using hmem'.symm

open TRS.Dev.LowerErrorEventShear TRS.Dev.LowerErrorEventShearPi in
lemma est_shear {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (n : ℕ) (ŵ : PriorSample s T d S Δ L → Vector d)
    (hŵ : @Measurable _ _ (priorInformation g n) inferInstance ŵ)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L))
    (ω1 : s.space) (u : PriorDraws S Δ L) (z : GaussianRows T d) :
    ŵ (ω1, u, z) = ŵ (ω1, Function.update u ℓ' (fun _ => zeroC),
      shearAll n (embedBlock S (levelAmplitude ℓ'.val • vecOf (u ℓ'))) z) := by
  refine est_factor g n ŵ hŵ _ _ rfl fun i hi => ?_
  have hsh := hiddenShift_update S Δ L ℓ' u
  simp only [priorTranscript, observations]
  have hz : shearAll n (embedBlock S (levelAmplitude ℓ'.val • vecOf (u ℓ'))) z i =
      rowShear (embedBlock S (levelAmplitude ℓ'.val • vecOf (u ℓ'))) (z i) := by
    simp [shearAll, rowG, hi]
  rw [hz]
  simp only [rowShear]
  refine Prod.ext rfl ?_
  simp only
  rw [hsh, embedBlock_add]
  simp only [inner_add_right]
  ring

end TRS.Dev.LowerErrorEventCore1

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventCore2

lemma measurable_update_pair {ι X : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace X] (i0 : ι) :
    Measurable (fun p : X × (ι → X) => Function.update p.2 i0 p.1) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i = i0
  · subst h; simpa using measurable_fst
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply i).comp measurable_snd

lemma update_map {ι X : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace X] (V : Measure X)
    [IsProbabilityMeasure V] (i0 : ι) :
    (V.prod (Measure.pi (fun _ : ι => V))).map (fun p : X × (ι → X) => Function.update p.2 i0 p.1) =
      Measure.pi (fun _ : ι => V) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_update_pair i0) (MeasurableSet.univ_pi hs)]
  have : (fun p : X × (ι → X) => Function.update p.2 i0 p.1) ⁻¹' (Set.univ.pi s) =
      (s i0) ×ˢ (Set.univ.pi (Function.update s i0 Set.univ)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i0, fun i => ?_⟩
      by_cases hi : i = i0
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = i0
      · subst hi; simpa using h1
      · simpa [Function.update_of_ne hi] using h2 i
  rw [this, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => V (s i)) (Finset.mem_univ i0),
    ← Finset.mul_prod_erase Finset.univ (fun i => V (Function.update s i0 Set.univ i)) (Finset.mem_univ i0)]
  simp only [Function.update_self, measure_univ, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end TRS.Dev.LowerErrorEventCore2

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventCore3

instance instProbU {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    IsProbabilityMeasure (uniformLevels S Δ L) := by
  unfold uniformLevels; infer_instance

instance instProbG (T d : ℕ) : IsProbabilityMeasure (gaussianRows T d) := by
  unfold gaussianRows; infer_instance

lemma lintegral_priorLaw {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (f : PriorSample s T d S Δ L → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂(priorLaw s T d S Δ L) =
      ∫⁻ ω1, ∫⁻ u, ∫⁻ z, f (ω1, u, z) ∂(gaussianRows T d) ∂(uniformLevels S Δ L) ∂s.law := by
  unfold priorLaw
  rw [lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun ω1 => ?_
  rw [lintegral_prod (fun y : PriorDraws S Δ L × GaussianRows T d => f (ω1, y)) (hf.comp measurable_prodMk_left).aemeasurable]

open TRS.Dev.LowerErrorEventCube TRS.Dev.LowerErrorEventCore1 in
lemma ball_cube {d : ℕ} (S : Finset (Fin d)) (c : BlockVector S) (a : ℝ) (ha : 0 < a) :
    (Measure.pi (fun _ : S => uniformCoordinate))
      {v : S → CubeCoordinate | ‖c - a • vecOf v‖ ≤ a * Real.sqrt S.card / 16} ≤
      ENNReal.ofReal ((1293 / 10000 : ℝ) ^ S.card) := by
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : S => uniformCoordinate)) := inferInstance
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  have hsub : {v : S → CubeCoordinate | ‖c - a • vecOf v‖ ≤ a * Real.sqrt S.card / 16} ⊆
      {v : S → CubeCoordinate | ∑ i, ((v i).val - c i / a) ^ 2 ≤ (S.card : ℝ) / 256} := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    have h1 : ‖c - a • vecOf v‖ ^ 2 ≤ (a * Real.sqrt S.card / 16) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hv 2
    have hρ : (a * Real.sqrt S.card / 16) ^ 2 = a ^ 2 * (S.card / 256) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), hρ] at h1
    have h2 : ∑ i : S, ‖(c - a • vecOf v) i‖ ^ 2 = a ^ 2 * ∑ i, ((v i).val - c i / a) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, PiLp.smul_apply, vecOf, smul_eq_mul]
      field_simp
      ring
    rw [h2] at h1
    have : a ^ 2 * ∑ i, ((v i).val - c i / a) ^ 2 ≤ a ^ 2 * (S.card / 256) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hc := cube_ball (fun i : S => c i / a)
  rw [Fintype.card_coe] at hc
  exact (measureReal_mono hsub (by simp)).trans hc

open TRS.Dev.LowerErrorEventCore1 TRS.Dev.LowerErrorEventCore2 TRS.Dev.LowerErrorEventLevels

lemma amp_pos' (ℓ : ℤ) : 0 < levelAmplitude ℓ := amp_pos ℓ

lemma measurable_blockProjection {d : ℕ} (S : Finset (Fin d)) : Measurable (blockProjection S) := by
  unfold blockProjection
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  exact (measurable_pi_apply i.val).comp (PiLp.continuous_ofLp 2 _).measurable

def u0 {d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (u : PriorDraws S Δ L) : PriorDraws S Δ L :=
  Function.update u ℓ' (fun _ => zeroC)

lemma measurable_u0 {d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) : Measurable (u0 (S := S) (Δ := Δ) (L := L) ℓ') := by
  have := (measurable_update_pair (X := S → CubeCoordinate) ℓ').comp
    ((measurable_const (a := (fun _ => zeroC : S → CubeCoordinate))).prodMk measurable_id)
  exact this

/-- The "reduced success" set: success for the sheared data. -/
def psiSet {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ŵ : PriorSample s T d S Δ L → Vector d) (gS : BlockVector S)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (ρ : ℝ) : Set (PriorSample s T d S Δ L) :=
  {ω | ‖blockProjection S (ŵ (ω.1, u0 ℓ' ω.2.1, ω.2.2)) - gS - hiddenShift S Δ L (u0 ℓ' ω.2.1)
      - levelAmplitude ℓ'.val • vecOf (ω.2.1 ℓ')‖ ≤ ρ}

lemma measurableSet_psiSet {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ŵ : PriorSample s T d S Δ L → Vector d) (hŵ : Measurable ŵ) (gS : BlockVector S)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (ρ : ℝ) :
    MeasurableSet (psiSet ŵ gS ℓ' ρ) := by
  unfold psiSet
  have h1 : Measurable fun ω : PriorSample s T d S Δ L => ŵ (ω.1, u0 ℓ' ω.2.1, ω.2.2) :=
    hŵ.comp (measurable_fst.prodMk (((measurable_u0 ℓ').comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))
  have h2 : Measurable fun ω : PriorSample s T d S Δ L => hiddenShift S Δ L (u0 ℓ' ω.2.1) :=
    (measurable_hiddenShift S Δ L).comp ((measurable_u0 ℓ').comp (measurable_fst.comp measurable_snd))
  have h3 : Measurable fun ω : PriorSample s T d S Δ L => vecOf (ω.2.1 ℓ') :=
    measurable_vecOf.comp ((measurable_pi_apply ℓ').comp (measurable_fst.comp measurable_snd))
  have h4 : Measurable fun ω : PriorSample s T d S Δ L =>
      blockProjection S (ŵ (ω.1, u0 ℓ' ω.2.1, ω.2.2)) - gS - hiddenShift S Δ L (u0 ℓ' ω.2.1)
        - levelAmplitude ℓ'.val • vecOf (ω.2.1 ℓ') :=
    (((measurable_blockProjection S).comp h1).sub_const gS |>.sub h2).sub (h3.const_smul (levelAmplitude ℓ'.val))
  exact measurableSet_le h4.norm measurable_const

lemma psi_slice {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ŵ : PriorSample s T d S Δ L → Vector d) (hŵ : Measurable ŵ) (gS : BlockVector S)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (ρ : ℝ)
    (hρ : ρ = levelAmplitude ℓ'.val * Real.sqrt S.card / 16)
    (ω1 : s.space) (z : GaussianRows T d) :
    uniformLevels S Δ L {u | (ω1, u, z) ∈ psiSet ŵ gS ℓ' ρ} ≤
      ENNReal.ofReal ((1293 / 10000 : ℝ) ^ S.card) := by
  set A : Set (PriorDraws S Δ L) := {u | (ω1, u, z) ∈ psiSet ŵ gS ℓ' ρ} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_psiSet ŵ hŵ gS ℓ' ρ).preimage (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hU : uniformLevels S Δ L = Measure.pi (fun _ : ↥(Finset.Icc (firstLevel S.card Δ) L) =>
      Measure.pi (fun _ : S => uniformCoordinate)) := rfl
  have hmap := update_map (Measure.pi (fun _ : S => uniformCoordinate)) ℓ'
  rw [← hU] at hmap
  rw [← hmap, Measure.map_apply (measurable_update_pair ℓ') hAm,
    Measure.prod_apply_symm ((measurable_update_pair ℓ') hAm)]
  calc ∫⁻ u', (Measure.pi (fun _ : S => uniformCoordinate))
        ((fun v => (v, u')) ⁻¹' ((fun p : (S → CubeCoordinate) × PriorDraws S Δ L =>
          Function.update p.2 ℓ' p.1) ⁻¹' A)) ∂(uniformLevels S Δ L)
      ≤ ∫⁻ _u', ENNReal.ofReal ((1293 / 10000 : ℝ) ^ S.card) ∂(uniformLevels S Δ L) := by
        refine lintegral_mono fun u' => ?_
        refine le_trans (measure_mono ?_) (ball_cube S
          (blockProjection S (ŵ (ω1, u0 ℓ' u', z)) - gS - hiddenShift S Δ L (u0 ℓ' u'))
          (levelAmplitude ℓ'.val) (amp_pos' ℓ'.val))
        intro v hv
        simp only [Set.mem_preimage, hA, psiSet, Set.mem_setOf_eq] at hv ⊢
        have h1 : u0 ℓ' (Function.update u' ℓ' v) = u0 ℓ' u' := by
          simp [u0, Function.update_idem]
        rw [h1] at hv
        simpa [hρ] using hv
    _ = _ := by simp

lemma psi_bound {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ŵ : PriorSample s T d S Δ L → Vector d) (hŵ : Measurable ŵ) (gS : BlockVector S)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (ρ : ℝ)
    (hρ : ρ = levelAmplitude ℓ'.val * Real.sqrt S.card / 16) :
    priorLaw s T d S Δ L (psiSet ŵ gS ℓ' ρ) ≤ ENNReal.ofReal ((1293 / 10000 : ℝ) ^ S.card) := by
  have hm := measurableSet_psiSet ŵ hŵ gS ℓ' ρ
  rw [← lintegral_indicator_one hm, lintegral_priorLaw _ (measurable_one.indicator hm)]
  calc ∫⁻ ω1, ∫⁻ u, ∫⁻ z, (psiSet ŵ gS ℓ' ρ).indicator 1 (ω1, u, z) ∂(gaussianRows T d)
        ∂(uniformLevels S Δ L) ∂s.law
      ≤ ∫⁻ _ω1, ENNReal.ofReal ((1293 / 10000 : ℝ) ^ S.card) ∂s.law := by
        refine lintegral_mono fun ω1 => ?_
        have hmm : Measurable (Function.uncurry fun (u : PriorDraws S Δ L) (z : GaussianRows T d) =>
            (psiSet ŵ gS ℓ' ρ).indicator (1 : PriorSample s T d S Δ L → ℝ≥0∞) (ω1, u, z)) :=
          (measurable_one.indicator hm).comp (measurable_const.prodMk measurable_id)
        rw [lintegral_lintegral_swap hmm.aemeasurable]
        calc ∫⁻ z, ∫⁻ u, (psiSet ŵ gS ℓ' ρ).indicator 1 (ω1, u, z) ∂(uniformLevels S Δ L)
              ∂(gaussianRows T d)
            ≤ ∫⁻ _z, ENNReal.ofReal ((1293 / 10000 : ℝ) ^ S.card) ∂(gaussianRows T d) := by
              refine lintegral_mono fun z => ?_
              have hs : MeasurableSet {u : PriorDraws S Δ L | (ω1, u, z) ∈ psiSet ŵ gS ℓ' ρ} :=
                hm.preimage (measurable_const.prodMk (measurable_id.prodMk measurable_const))
              have := lintegral_indicator_one (μ := uniformLevels S Δ L) hs
              have h2 : ∫⁻ u, (psiSet ŵ gS ℓ' ρ).indicator 1 (ω1, u, z) ∂(uniformLevels S Δ L) =
                  uniformLevels S Δ L {u | (ω1, u, z) ∈ psiSet ŵ gS ℓ' ρ} := by
                rw [← this]
                refine lintegral_congr fun u => ?_
                by_cases h : (ω1, u, z) ∈ psiSet ŵ gS ℓ' ρ <;> simp [h, Set.indicator]
              rw [h2]
              exact psi_slice ŵ hŵ gS ℓ' ρ hρ ω1 z
          _ = _ := by simp
    _ = _ := by simp

open TRS.Dev.LowerErrorEventShear TRS.Dev.LowerErrorEventShearPi

lemma measurable_densityAll_joint {T d : ℕ} (n : ℕ) :
    Measurable (fun p : Vector d × GaussianRows T d => densityAll n p.1 p.2) := by
  unfold densityAll
  refine Finset.measurable_prod _ fun i _ => ?_
  unfold rowF
  by_cases h : i.val < n
  · simp only [h, if_true]
    unfold rowD
    have hx : Measurable fun p : Vector d × GaussianRows T d => (p.2 i).1 :=
      measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
    have he : Measurable fun p : Vector d × GaussianRows T d => (p.2 i).2 :=
      measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)
    have hin : Measurable fun p : Vector d × GaussianRows T d => inner ℝ (p.2 i).1 p.1 :=
      hx.inner measurable_fst
    exact (he.mul hin |>.sub ((hin.pow_const 2).div_const 2)).exp
  · simp [h]

def eL {d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (u : PriorDraws S Δ L) : Vector d :=
  embedBlock S (levelAmplitude ℓ'.val • vecOf (u ℓ'))

lemma measurable_eL {d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) : Measurable (eL (S := S) (Δ := Δ) (L := L) ℓ') := by
  unfold eL
  exact (measurable_embedBlock S).comp
    ((measurable_vecOf.comp (measurable_pi_apply ℓ')).const_smul (levelAmplitude ℓ'.val))

lemma mem_iff_shear {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (n : ℕ) (ŵ : PriorSample s T d S Δ L → Vector d)
    (hŵn : @Measurable _ _ (priorInformation g n) inferInstance ŵ) (gS : BlockVector S)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (ρ : ℝ)
    (ω1 : s.space) (u : PriorDraws S Δ L) (z : GaussianRows T d) :
    ‖blockProjection S (ŵ (ω1, u, z)) - gS - hiddenShift S Δ L u‖ ≤ ρ ↔
      (ω1, u, shearAll n (eL ℓ' u) z) ∈ psiSet ŵ gS ℓ' ρ := by
  have h1 := est_shear g n ŵ hŵn ℓ' ω1 u z
  have h2 := hiddenShift_update S Δ L ℓ' u
  simp only [psiSet, Set.mem_setOf_eq]
  have h3 : ŵ (ω1, u, z) = ŵ (ω1, u0 ℓ' u, shearAll n (eL ℓ' u) z) := h1
  rw [h3, h2]
  rw [sub_add_eq_sub_sub]
  rfl

lemma change_of_measure {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (n : ℕ) (ŵ : PriorSample s T d S Δ L → Vector d)
    (hŵn : @Measurable _ _ (priorInformation g n) inferInstance ŵ) (gS : BlockVector S)
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (ρ : ℝ) :
    priorLaw s T d S Δ L {ω | ‖blockProjection S (ŵ ω) - gS - hiddenShift S Δ L ω.2.1‖ ≤ ρ} =
      ∫⁻ ω, ENNReal.ofReal (densityAll n (eL ℓ' ω.2.1) ω.2.2) *
        (psiSet ŵ gS ℓ' ρ).indicator 1 ω ∂(priorLaw s T d S Δ L) := by
  have hŵ : Measurable ŵ := hŵn.mono (priorInformation_le g n) le_rfl
  have hA : MeasurableSet {ω : PriorSample s T d S Δ L |
      ‖blockProjection S (ŵ ω) - gS - hiddenShift S Δ L ω.2.1‖ ≤ ρ} := by
    have h4 : Measurable fun ω : PriorSample s T d S Δ L =>
        blockProjection S (ŵ ω) - gS - hiddenShift S Δ L ω.2.1 :=
      ((measurable_blockProjection S).comp hŵ).sub_const gS |>.sub
        ((measurable_hiddenShift S Δ L).comp (measurable_fst.comp measurable_snd))
    exact measurableSet_le h4.norm measurable_const
  have hm := measurableSet_psiSet ŵ hŵ gS ℓ' ρ
  have hD : Measurable fun ω : PriorSample s T d S Δ L =>
      ENNReal.ofReal (densityAll n (eL ℓ' ω.2.1) ω.2.2) :=
    ((measurable_densityAll_joint n).comp (((measurable_eL ℓ').comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))).ennreal_ofReal
  rw [← lintegral_indicator_one hA, lintegral_priorLaw _ (measurable_one.indicator hA),
    lintegral_priorLaw (fun ω => ENNReal.ofReal (densityAll n (eL ℓ' ω.2.1) ω.2.2) *
      (psiSet ŵ gS ℓ' ρ).indicator 1 ω) (hD.mul (measurable_one.indicator hm))]
  refine lintegral_congr fun ω1 => lintegral_congr fun u => ?_
  have hF : Measurable fun z : GaussianRows T d => (psiSet ŵ gS ℓ' ρ).indicator
      (1 : PriorSample s T d S Δ L → ℝ≥0∞) (ω1, u, z) :=
    (measurable_one.indicator hm).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have := shear_lintegral n (eL ℓ' u) _ hF
  rw [show (∫⁻ z, ENNReal.ofReal (densityAll n (eL ℓ' u) z) *
      (psiSet ŵ gS ℓ' ρ).indicator 1 (ω1, u, z) ∂(gaussianRows T d)) = _ from this.symm]
  refine lintegral_congr fun z => ?_
  have := mem_iff_shear g n ŵ hŵn gS ℓ' ρ ω1 u z
  by_cases h : ‖blockProjection S (ŵ (ω1, u, z)) - gS - hiddenShift S Δ L u‖ ≤ ρ
  · have h' := this.1 h
    simp [Set.indicator, h, h']
  · have h' : (ω1, u, shearAll n (eL ℓ' u) z) ∉ psiSet ŵ gS ℓ' ρ := fun hh => h (this.2 hh)
    simp [Set.indicator, h, h']

lemma invsqrt_pow_le (y : ℝ) (n : ℕ) (hy : 0 < y) :
    (1 / Real.sqrt y) ^ n ≤ Real.exp (n * (1 / y - 1) / 2) := by
  have h1 : 1 / Real.sqrt y = Real.exp (Real.log (1 / y) / 2) := by
    rw [one_div, ← Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 1; ring
  rw [h1, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have := Real.log_le_sub_one_of_pos (show 0 < 1 / y by positivity)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma D_numeric (a : ℝ) (k n : ℕ) (e2 : ℝ) (he0 : 0 ≤ e2) (he : e2 ≤ a ^ 2 * k)
    (hq : a ^ 2 * k ≤ 1 / 16384) (hna : (n : ℝ) * a ^ 2 ≤ 1 / 1024) :
    (1 / Real.sqrt (1 - 2 * e2)) ^ n ≤ (1002 / 1000 : ℝ) ^ k := by
  have hy : 0 < 1 - 2 * e2 := by linarith
  refine (invsqrt_pow_le _ n hy).trans ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 1 / (1 - 2 * e2) - 1 ≤ 2 * (a ^ 2 * k) * (8192 / 8191) := by
    rw [div_sub_one hy.ne', div_le_iff₀ hy]
    nlinarith
  have h2 : (n : ℝ) * (1 / (1 - 2 * e2) - 1) / 2 ≤ (k : ℝ) / 1000 := by
    have : (n : ℝ) * (1 / (1 - 2 * e2) - 1) / 2 ≤ n * (2 * (a ^ 2 * k) * (8192 / 8191)) / 2 := by
      gcongr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : (n : ℝ) * (2 * (a ^ 2 * k) * (8192 / 8191)) / 2 = (n * a ^ 2) * k * (8192 / 8191) := by ring
    rw [h3] at this
    have h4 : (n * a ^ 2 : ℝ) * k * (8192 / 8191) ≤ (1 / 1024) * k * (8192 / 8191) := by gcongr
    nlinarith
  calc Real.exp ((n : ℝ) * (1 / (1 - 2 * e2) - 1) / 2) ≤ Real.exp ((k : ℝ) / 1000) :=
        Real.exp_le_exp.2 h2
    _ = Real.exp (1 / 1000) ^ k := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ (1002 / 1000 : ℝ) ^ k := by
        apply pow_le_pow_left₀ (Real.exp_pos _).le
        have := Real.add_one_le_exp (-(1 / 1000 : ℝ))
        have h5 : Real.exp (-(1 / 1000 : ℝ)) * Real.exp (1 / 1000) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (1 / 1000 : ℝ)]

lemma norm_eL_sq_le {d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L)) (u : PriorDraws S Δ L) :
    ‖eL ℓ' u‖ ^ 2 ≤ levelAmplitude ℓ'.val ^ 2 * S.card := by
  unfold eL
  rw [norm_embedBlock, norm_smul, Real.norm_eq_abs, abs_of_pos (amp_pos _), mul_pow]
  gcongr
  have := vec_norm_le S (u ℓ')
  calc ‖vecOf (u ℓ')‖ ^ 2 ≤ (Real.sqrt S.card) ^ 2 := by
        gcongr
        exact this
    _ = (S.card : ℝ) := Real.sq_sqrt (by positivity)

lemma D_sq_bound {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (n : ℕ) (hn : n ≤ T) (ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L))
    (hq : levelAmplitude ℓ'.val ^ 2 * S.card ≤ 1 / 16384)
    (hna : (n : ℝ) * levelAmplitude ℓ'.val ^ 2 ≤ 1 / 1024) :
    ∫⁻ ω, ENNReal.ofReal (densityAll n (eL ℓ' ω.2.1) ω.2.2) ^ 2 ∂(priorLaw s T d S Δ L) ≤
      ENNReal.ofReal ((1002 / 1000 : ℝ) ^ S.card) := by
  have hD : Measurable fun ω : PriorSample s T d S Δ L =>
      ENNReal.ofReal (densityAll n (eL ℓ' ω.2.1) ω.2.2) ^ 2 :=
    (((measurable_densityAll_joint n).comp (((measurable_eL ℓ').comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))).ennreal_ofReal).pow_const 2
  rw [lintegral_priorLaw _ hD]
  calc ∫⁻ ω1, ∫⁻ u, ∫⁻ z, ENNReal.ofReal (densityAll n (eL ℓ' u) z) ^ 2 ∂(gaussianRows T d)
        ∂(uniformLevels S Δ L) ∂s.law
      ≤ ∫⁻ _ω1, ∫⁻ _u, ENNReal.ofReal ((1002 / 1000 : ℝ) ^ S.card) ∂(uniformLevels S Δ L) ∂s.law := by
        refine lintegral_mono fun ω1 => lintegral_mono fun u => ?_
        have h2 : 2 * ‖eL ℓ' u‖ ^ 2 < 1 := by
          have := norm_eL_sq_le ℓ' u
          linarith
        rw [densityAll_sq_lintegral n hn _ h2]
        exact ENNReal.ofReal_le_ofReal (D_numeric _ _ _ _ (by positivity) (norm_eL_sq_le ℓ' u) hq hna)
    _ = _ := by simp

end TRS.Dev.LowerErrorEventCore3

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventPart2

open TRS.Dev.LowerErrorEventCore3 TRS.Dev.LowerErrorEventLevels
  TRS.Dev.LowerErrorEventCore1 TRS.Dev.LowerErrorEventShearPi

lemma final_numeric (k : ℕ) :
    (1002 / 1000 : ℝ) ^ k * (1293 / 10000 : ℝ) ^ k ≤ ((9 / 25 : ℝ) ^ k) ^ 2 := by
  rw [← mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
  apply pow_le_pow_left₀ (by positivity)
  norm_num

theorem part2 {s : RandomSeed} {T d : ℕ} (S : Finset (Fin d)) (hS : 0 < S.card) (Δ : ℝ) (hΔ : 0 < Δ)
    (hΔ₁ : Δ ≤ 1) (L : ℤ) (g : Fin T → Vector d) (gS : BlockVector S)
    (ℓ : ℤ) (hℓ0 : firstLevel S.card Δ ≤ ℓ) (hℓL : ℓ ≤ L)
    (n : ℕ) (hnT : n ≤ T) (hn2 : (n : ℝ) ≤ (2 : ℝ) ^ ℓ)
    (ŵ : PriorSample s T d S Δ L → Vector d)
    (hŵ : @Measurable _ _ (priorInformation g n) inferInstance ŵ) :
    priorLaw s T d S Δ L {ω |
      ‖blockProjection S (ŵ ω) - gS - hiddenShift S Δ L ω.2.1‖ ≤
        levelAmplitude ℓ * Real.sqrt S.card / 16} ≤
      ENNReal.ofReal ((9 / 25 : ℝ) ^ S.card) := by
  set ℓ' : ↥(Finset.Icc (firstLevel S.card Δ) L) := ⟨ℓ, Finset.mem_Icc.2 ⟨hℓ0, hℓL⟩⟩ with hℓ'
  have hŵ' : Measurable ŵ := hŵ.mono (priorInformation_le g n) le_rfl
  have hk : (0 : ℝ) < S.card := by exact_mod_cast hS
  have h2l : 16 * (S.card : ℝ) ≤ (2 : ℝ) ^ ℓ := by
    have := two_zpow_firstLevel_ge S.card Δ hS hΔ ℓ hℓ0
    have h1 : 16 * (S.card : ℝ) ≤ 16 * (S.card : ℝ) / Δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hΔ2 : Δ ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hΔ2 hk.le]
    linarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have ha2 : levelAmplitude ℓ ^ 2 = (1 / 1024) * ((2 : ℝ) ^ ℓ)⁻¹ := by
    rw [amp_sq, zpow_neg (2 : ℝ) ℓ]; norm_num
  have hq : levelAmplitude ℓ'.val ^ 2 * S.card ≤ 1 / 16384 := by
    show levelAmplitude ℓ ^ 2 * S.card ≤ 1 / 16384
    rw [ha2]
    have : (S.card : ℝ) * ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 / 16 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpow]; linarith
    nlinarith
  have hna : (n : ℝ) * levelAmplitude ℓ'.val ^ 2 ≤ 1 / 1024 := by
    show (n : ℝ) * levelAmplitude ℓ ^ 2 ≤ 1 / 1024
    rw [ha2]
    have : (n : ℝ) * ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hpow]; exact hn2
    nlinarith
  rw [change_of_measure g n ŵ hŵ gS ℓ' _]
  set μ := priorLaw s T d S Δ L
  have hm := measurableSet_psiSet ŵ hŵ' gS ℓ' (levelAmplitude ℓ * Real.sqrt S.card / 16)
  have hD : Measurable fun ω : PriorSample s T d S Δ L =>
      ENNReal.ofReal (densityAll n (eL ℓ' ω.2.1) ω.2.2) :=
    ((measurable_densityAll_joint n).comp (((measurable_eL ℓ').comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))).ennreal_ofReal
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun ω : PriorSample s T d S Δ L => ENNReal.ofReal (densityAll n (eL ℓ' ω.2.1) ω.2.2))
    (g := (psiSet ŵ gS ℓ' (levelAmplitude ℓ * Real.sqrt S.card / 16)).indicator 1)
    hD.aemeasurable (measurable_one.indicator hm).aemeasurable
  refine hCS.trans ?_
  have hDb := D_sq_bound (s := s) (S := S) (Δ := Δ) (L := L) (d := d) n hnT ℓ' hq hna
  have hPb := psi_bound ŵ hŵ' gS ℓ' (levelAmplitude ℓ * Real.sqrt S.card / 16) rfl
  have e1 : ∫⁻ a, ENNReal.ofReal (densityAll n (eL ℓ' a.2.1) a.2.2) ^ (2 : ℝ) ∂μ =
      ∫⁻ a, ENNReal.ofReal (densityAll n (eL ℓ' a.2.1) a.2.2) ^ 2 ∂μ := by
    simp_rw [ENNReal.rpow_two]
  have e2 : ∫⁻ a, ((psiSet ŵ gS ℓ' (levelAmplitude ℓ * Real.sqrt S.card / 16)).indicator
      (1 : PriorSample s T d S Δ L → ℝ≥0∞) a) ^ (2 : ℝ) ∂μ =
      μ (psiSet ŵ gS ℓ' (levelAmplitude ℓ * Real.sqrt S.card / 16)) := by
    rw [← lintegral_indicator_one hm]
    refine lintegral_congr fun a => ?_
    by_cases h : a ∈ psiSet ŵ gS ℓ' (levelAmplitude ℓ * Real.sqrt S.card / 16) <;>
      simp [Set.indicator, h]
  rw [e1, e2]
  calc (∫⁻ a, ENNReal.ofReal (densityAll n (eL ℓ' a.2.1) a.2.2) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
        (μ (psiSet ŵ gS ℓ' (levelAmplitude ℓ * Real.sqrt S.card / 16))) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal ((1002 / 1000 : ℝ) ^ S.card)) ^ (1 / (2 : ℝ)) *
        (ENNReal.ofReal ((1293 / 10000 : ℝ) ^ S.card)) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = (ENNReal.ofReal ((1002 / 1000 : ℝ) ^ S.card * (1293 / 10000 : ℝ) ^ S.card)) ^ (1 / (2 : ℝ)) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_mul (by positivity)]
    _ ≤ (ENNReal.ofReal (((9 / 25 : ℝ) ^ S.card) ^ 2)) ^ (1 / (2 : ℝ)) := by
        gcongr
        exact final_numeric S.card
    _ = ENNReal.ofReal ((9 / 25 : ℝ) ^ S.card) := by
        rw [ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end TRS.Dev.LowerErrorEventPart2

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventPart3

open TRS.Dev.LowerErrorEventLevels

lemma level_choice (k : ℕ) (Δ : ℝ) (hk : 0 < k) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) (L : ℤ)
    (hL : firstLevel k Δ ≤ L) (T : ℕ) (hLT : (T : ℝ) ≤ (2 : ℝ) ^ L) (date : ℕ) (hd : date < T) :
    ∃ ℓ : ℤ, firstLevel k Δ ≤ ℓ ∧ ℓ ≤ L ∧ (date : ℝ) ≤ (2 : ℝ) ^ ℓ ∧
      (2 : ℝ) ^ ℓ < 2 * max (date : ℝ) (16 * (k : ℝ) / Δ ^ 2) := by
  have hx : 0 < 16 * (k : ℝ) / Δ ^ 2 := by positivity
  have hge := two_zpow_firstLevel_ge k Δ hk hΔ _ le_rfl
  have hlt := two_zpow_firstLevel_lt k Δ hk hΔ
  have h16 : 16 ≤ 16 * (k : ℝ) / Δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hΔ2 : Δ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  by_cases h1 : (date : ℝ) ≤ (2 : ℝ) ^ (firstLevel k Δ)
  · refine ⟨firstLevel k Δ, le_rfl, hL, h1, ?_⟩
    calc (2 : ℝ) ^ (firstLevel k Δ) < 2 * (16 * (k : ℝ) / Δ ^ 2) := hlt
      _ ≤ 2 * max (date : ℝ) (16 * (k : ℝ) / Δ ^ 2) := by
        gcongr; exact le_max_right _ _
  · push Not at h1
    -- date > 2^ℓ0 ≥ 16, so date ≥ 2
    have hdate : 16 < (date : ℝ) := lt_of_le_of_lt (h16.trans hge) h1
    have hdate2 : 2 ≤ date := by
      have : (16 : ℝ) < date := hdate
      exact_mod_cast (by exact_mod_cast this.le : (16 : ℕ) ≤ date) |>.trans' (by norm_num)
    set c := Nat.clog 2 date with hc
    have hc1 : date ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) date
    have hc2 : 2 ^ (c - 1) < date := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    have hc3 : (2 : ℝ) ^ (c : ℤ) < 2 * (date : ℝ) := by
      have hcpos : 1 ≤ c := by
        rw [hc]; exact Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
      have : (2 : ℕ) ^ c = 2 * 2 ^ (c - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h4 : ((2 : ℕ) ^ c : ℕ) < 2 * date := by rw [this]; omega
      rw [zpow_natCast]
      exact_mod_cast h4
    have hc4 : (date : ℝ) ≤ (2 : ℝ) ^ (c : ℤ) := by
      rw [zpow_natCast]; exact_mod_cast hc1
    have hcL : (c : ℤ) ≤ L := by
      have hL0 : (0 : ℤ) ≤ L := by
        have h2 : (0 : ℝ) < 2 ^ firstLevel k Δ := by positivity
        by_contra hneg
        push Not at hneg
        have : (2 : ℝ) ^ L < 1 := zpow_lt_one_of_neg₀ (by norm_num) hneg
        have h5 : (2 : ℝ) ^ (firstLevel k Δ) ≤ (2 : ℝ) ^ L :=
          zpow_le_zpow_right₀ (by norm_num) hL
        linarith [h16.trans hge]
      have hLn : (2 : ℝ) ^ L = (2 : ℝ) ^ L.toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hL0]
      have : date ≤ 2 ^ L.toNat := by
        have : (date : ℝ) ≤ (2 : ℝ) ^ L.toNat := by
          rw [← hLn]
          have : (date : ℝ) < T := by exact_mod_cast hd
          linarith
        exact_mod_cast this
      have h6 : c ≤ L.toNat := Nat.clog_le_of_le_pow this
      omega
    have hc0 : firstLevel k Δ ≤ (c : ℤ) := by
      by_contra hneg
      push Not at hneg
      have : (2 : ℝ) ^ (c : ℤ) < (2 : ℝ) ^ (firstLevel k Δ) :=
        zpow_lt_zpow_right₀ (by norm_num) hneg
      linarith
    refine ⟨c, hc0, hcL, hc4, ?_⟩
    calc (2 : ℝ) ^ (c : ℤ) < 2 * (date : ℝ) := hc3
      _ ≤ 2 * max (date : ℝ) (16 * (k : ℝ) / Δ ^ 2) := by
        gcongr; exact le_max_left _ _

open TRS.Dev.LowerErrorEventCore1 TRS.Dev.LowerErrorEventCore3 TRS.Dev.LowerErrorEventPart2 in
theorem part3 {s : RandomSeed} {T d : ℕ} (S : Finset (Fin d)) (hS : 0 < S.card) (Δ : ℝ) (hΔ : 0 < Δ)
    (hΔ₁ : Δ ≤ 1) (L : ℤ) (hL : firstLevel S.card Δ ≤ L) (hLT : (T : ℝ) ≤ (2 : ℝ) ^ L)
    (g : Fin T → Vector d) (gS : BlockVector S) (B : ℕ) (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) :
    ∃ E : Set (PriorSample s T d S Δ L), MeasurableSet E ∧
      ENNReal.ofReal (1 - (B : ℝ) * ((L - firstLevel S.card Δ + 1 : ℤ) : ℝ) *
        (9 / 25 : ℝ) ^ S.card) ≤ priorLaw s T d S Δ L E ∧
      ∀ ω ∈ E, ∀ j : Fin B, π.date j (priorTranscript g ω) < T →
        (2 : ℝ) ^ (-19 : ℤ) * S.card /
          max (π.date j (priorTranscript g ω) : ℝ) (16 * S.card / Δ ^ 2) ≤
        ‖blockProjection S (π.head j (priorTranscript g ω)) - gS -
          hiddenShift S Δ L ω.2.1‖ ^ 2 := by
  classical
  set μ := priorLaw s T d S Δ L with hμ
  set ℓ0 := firstLevel S.card Δ with hℓ0
  set N : Finset ℤ := Finset.Icc ℓ0 L with hN
  set nℓ : ℤ → ℕ := fun ℓ => min T ⌊(2 : ℝ) ^ ℓ⌋₊ with hnℓ
  set est : Fin B → ℤ → PriorSample s T d S Δ L → Vector d := fun j ℓ ω =>
    if π.date j (priorTranscript g ω) ≤ nℓ ℓ then π.head j (priorTranscript g ω) else 0 with hest
  let Bad : Fin B → ℤ → Set (PriorSample s T d S Δ L) := fun j ℓ =>
    {ω | π.date j (priorTranscript g ω) ≤ nℓ ℓ ∧
      ‖blockProjection S (π.head j (priorTranscript g ω)) - gS - hiddenShift S Δ L ω.2.1‖ ≤
        levelAmplitude ℓ * Real.sqrt S.card / 16}
  have hpt := measurable_priorTranscript (s := s) (S := S) (Δ := Δ) (L := L) g
  -- measurability of date and head
  have hdate : ∀ (j : Fin B) (n : ℕ), MeasurableSet {ω : PriorSample s T d S Δ L |
      π.date j (priorTranscript g ω) ≤ n} := by
    intro j n
    have h := hπ.2.2.1 j n
    have h2 : MeasurableSet[(inferInstance : MeasurableSpace (Transcript s T d))]
        {ω : Transcript s T d | π.date j ω ≤ n} := by
      have hF : Measurable (fun ω : Transcript s T d =>
          (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) := by
        refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
        by_cases h : i.val < n
        · simp only [h, if_true]
          exact (measurable_pi_apply i).comp measurable_snd
        · simp [h]
      exact hF.comap_le _ h
    exact hpt h2
  have hhead : ∀ j : Fin B, Measurable (fun ω : PriorSample s T d S Δ L =>
      π.head j (priorTranscript g ω)) := by
    intro j
    have h := hπ.2.2.2 j T
    have hF : Measurable (fun ω : Transcript s T d =>
        (ω.1, fun i : Fin T => if i.val < T then ω.2 i else (0, 0))) := by
      refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
      by_cases h : i.val < T
      · simp only [h, if_true]
        exact (measurable_pi_apply i).comp measurable_snd
      · simp [h]
    have h2 : Measurable (fun ω : Transcript s T d => if π.date j ω ≤ T then π.head j ω else 0) :=
      h.mono hF.comap_le le_rfl
    have h3 : (fun ω : Transcript s T d => if π.date j ω ≤ T then π.head j ω else 0) = π.head j := by
      funext ω; simp [hπ.1 j ω]
    rw [h3] at h2
    exact h2.comp hpt
  have hBadm : ∀ j ℓ, MeasurableSet (Bad j ℓ) := by
    intro j ℓ
    refine (hdate j _).inter ?_
    have h4 : Measurable fun ω : PriorSample s T d S Δ L =>
        blockProjection S (π.head j (priorTranscript g ω)) - gS - hiddenShift S Δ L ω.2.1 :=
      ((measurable_blockProjection S).comp (hhead j)).sub_const gS |>.sub
        ((measurable_hiddenShift S Δ L).comp (measurable_fst.comp measurable_snd))
    exact measurableSet_le h4.norm measurable_const
  have hBadb : ∀ j, ∀ ℓ ∈ N, μ (Bad j ℓ) ≤ ENNReal.ofReal ((9 / 25 : ℝ) ^ S.card) := by
    intro j ℓ hℓ
    rw [hN, Finset.mem_Icc] at hℓ
    have hmeas : @Measurable _ _ (priorInformation g (nℓ ℓ)) inferInstance (est j ℓ) := by
      have h := hπ.2.2.2 j (nℓ ℓ)
      have hc : @Measurable (PriorSample s T d S Δ L) (Transcript s T d)
          (priorInformation g (nℓ ℓ)) (information s T d (nℓ ℓ))
          (priorTranscript g) := comap_measurable (priorTranscript g)
      exact h.comp hc
    have hn2 : ((nℓ ℓ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ℓ :=
      (Nat.cast_le.2 (min_le_right _ _)).trans (Nat.floor_le (by positivity))
    have := part2 (s := s) S hS Δ hΔ hΔ₁ L g gS ℓ hℓ.1 hℓ.2 (nℓ ℓ) (min_le_left _ _) hn2 (est j ℓ) hmeas
    refine le_trans (measure_mono ?_) this
    intro ω hω
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_setOf_eq, hest, if_pos h1]
    exact h2
  set U : Set (PriorSample s T d S Δ L) := ⋃ j : Fin B, ⋃ ℓ ∈ N, Bad j ℓ with hU
  have hUm : MeasurableSet U :=
    MeasurableSet.iUnion fun j => MeasurableSet.biUnion N.countable_toSet fun ℓ _ => hBadm j ℓ
  have hcardN : (N.card : ℝ) = ((L - ℓ0 + 1 : ℤ) : ℝ) := by
    rw [hN, Int.card_Icc]
    have : ((L + 1 - ℓ0).toNat : ℤ) = L - ℓ0 + 1 := by omega
    have h2 : (((L + 1 - ℓ0).toNat : ℕ) : ℝ) = (((L + 1 - ℓ0).toNat : ℤ) : ℝ) := by norm_cast
    rw [h2, this]
  have hμU : μ U ≤ ENNReal.ofReal ((B : ℝ) * ((L - ℓ0 + 1 : ℤ) : ℝ) * (9 / 25 : ℝ) ^ S.card) := by
    calc μ U ≤ ∑ j : Fin B, μ (⋃ ℓ ∈ N, Bad j ℓ) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ j : Fin B, ∑ ℓ ∈ N, μ (Bad j ℓ) :=
          Finset.sum_le_sum fun j _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ j : Fin B, ∑ ℓ ∈ N, ENNReal.ofReal ((9 / 25 : ℝ) ^ S.card) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ℓ hℓ => hBadb j ℓ hℓ
      _ = ENNReal.ofReal (∑ j : Fin B, ∑ ℓ ∈ N, (9 / 25 : ℝ) ^ S.card) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun ℓ _ => by positivity)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => by positivity)]
      _ = _ := by
          congr 1
          simp [Finset.sum_const, hcardN]
          ring
  refine ⟨Uᶜ, hUm.compl, ?_, ?_⟩
  · haveI : IsProbabilityMeasure μ := by rw [hμ]; unfold priorLaw; infer_instance
    rw [prob_compl_eq_one_sub hUm]
    have hX0 : 0 ≤ (B : ℝ) * ((L - ℓ0 + 1 : ℤ) : ℝ) * (9 / 25 : ℝ) ^ S.card := by
      have : (0 : ℝ) ≤ ((L - ℓ0 + 1 : ℤ) : ℝ) := by
        rw [← hcardN]; positivity
      positivity
    rw [ENNReal.ofReal_sub 1 hX0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hμU 1
  · intro ω hω j hd
    have hω' : ∀ ℓ ∈ N, ω ∉ Bad j ℓ := by
      intro ℓ hℓ hb
      exact hω (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion₂.2 ⟨ℓ, hℓ, hb⟩⟩)
    obtain ⟨ℓ, hℓ0', hℓL, hdℓ, hℓ2⟩ := level_choice S.card Δ hS hΔ hΔ₁ L hL T hLT _ hd
    have hℓN : ℓ ∈ N := by rw [hN, Finset.mem_Icc]; exact ⟨hℓ0', hℓL⟩
    have hnb := hω' ℓ hℓN
    have hdn : π.date j (priorTranscript g ω) ≤ nℓ ℓ := by
      refine le_min hd.le (Nat.le_floor ?_)
      exact hdℓ
    have hfar : levelAmplitude ℓ * Real.sqrt S.card / 16 <
        ‖blockProjection S (π.head j (priorTranscript g ω)) - gS - hiddenShift S Δ L ω.2.1‖ := by
      by_contra hcon
      push Not at hcon
      exact hnb ⟨hdn, hcon⟩
    have hk : (0 : ℝ) < S.card := by exact_mod_cast hS
    have hpow : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
    have hm : 0 < max (π.date j (priorTranscript g ω) : ℝ) (16 * S.card / Δ ^ 2) :=
      lt_max_of_lt_right (div_pos (by linarith) (by positivity))
    set m := max (π.date j (priorTranscript g ω) : ℝ) (16 * S.card / Δ ^ 2) with hmdef
    have hρ2 : (levelAmplitude ℓ * Real.sqrt S.card / 16) ^ 2 = (S.card : ℝ) / (2 ^ 18 * (2 : ℝ) ^ ℓ) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hk.le, amp_sq, zpow_neg (2 : ℝ) ℓ]
      field_simp
      norm_num
    have hle : (S.card : ℝ) / (2 ^ 18 * (2 : ℝ) ^ ℓ) ≥ (2 : ℝ) ^ (-19 : ℤ) * S.card / m := by
      rw [show (2 : ℝ) ^ (-19 : ℤ) = 1 / 2 ^ 19 by norm_num, ge_iff_le, div_le_div_iff₀ hm (by positivity)]
      nlinarith [hk, hℓ2, hpow]
    calc (2 : ℝ) ^ (-19 : ℤ) * S.card / m ≤ (S.card : ℝ) / (2 ^ 18 * (2 : ℝ) ^ ℓ) := hle
      _ = (levelAmplitude ℓ * Real.sqrt S.card / 16) ^ 2 := hρ2.symm
      _ ≤ _ := by
        apply pow_le_pow_left₀ (div_nonneg (mul_nonneg (amp_pos ℓ).le (Real.sqrt_nonneg _)) (by norm_num)) hfar.le

end TRS.Dev.LowerErrorEventPart3

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

namespace TRS

theorem chk_common_lower_error_event (T d : ℕ) (hT : 0 < T) (hd : 0 < d)
    (S : Finset (Fin d)) (hS : 0 < S.card) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1)
    (L : ℤ) (hL : firstLevel S.card Δ ≤ L) (hLT : (T : ℝ) ≤ (2 : ℝ) ^ L)
    (g : Fin T → Vector d) (gS : BlockVector S)
    (hg : ∀ i, blockProjection S (g i) = gS) (s : RandomSeed) :
    (∀ u : PriorDraws S Δ L, ‖hiddenShift S Δ L u‖ < Δ / 32) ∧
    (∀ ℓ : ℤ, firstLevel S.card Δ ≤ ℓ → ℓ ≤ L →
      ∀ n : ℕ, n ≤ T → (n : ℝ) ≤ (2 : ℝ) ^ ℓ →
      ∀ ŵ : PriorSample s T d S Δ L → Vector d,
        @Measurable _ _ (priorInformation g n) inferInstance ŵ →
        priorLaw s T d S Δ L {ω |
          ‖blockProjection S (ŵ ω) - gS - hiddenShift S Δ L ω.2.1‖ ≤
            levelAmplitude ℓ * Real.sqrt S.card / 16} ≤
          ENNReal.ofReal ((9 / 25 : ℝ) ^ S.card)) ∧
    (∀ B : ℕ, ∀ π : ReleasePolicy s T d B, IsCausal π →
      ∃ E : Set (PriorSample s T d S Δ L), MeasurableSet E ∧
        ENNReal.ofReal (1 - (B : ℝ) * ((L - firstLevel S.card Δ + 1 : ℤ) : ℝ) *
          (9 / 25 : ℝ) ^ S.card) ≤ priorLaw s T d S Δ L E ∧
        ∀ ω ∈ E, ∀ j : Fin B, π.date j (priorTranscript g ω) < T →
          (2 : ℝ) ^ (-19 : ℤ) * S.card /
            max (π.date j (priorTranscript g ω) : ℝ) (16 * S.card / Δ ^ 2) ≤
          ‖blockProjection S (π.head j (priorTranscript g ω)) - gS -
            hiddenShift S Δ L ω.2.1‖ ^ 2) := by
  refine ⟨fun u => TRS.Dev.LowerErrorEventLevels.part1 S hS Δ hΔ hΔ₁ L hL u, ?_, ?_⟩
  · intro ℓ hℓ0 hℓL n hnT hn2 ŵ hŵ
    exact TRS.Dev.LowerErrorEventPart2.part2 S hS Δ hΔ hΔ₁ L g gS ℓ hℓ0 hℓL n hnT hn2 ŵ hŵ
  · intro B π hπ
    exact TRS.Dev.LowerErrorEventPart3.part3 S hS Δ hΔ hΔ₁ L hL hLT g gS B π hπ

end TRS
end

theorem solution : type_of% @TRS.chk_common_lower_error_event := @TRS.chk_common_lower_error_event
