-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P13.exponential_vector
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T03:05:29.735888+00:00
-- url     : https://prove2.me/submissions/2fe605ed-951f-4d8b-a436-8dfeb5a311ef

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13
noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

open Nat in
theorem g75h_coef_norm_sq (z : ℂ) (n : ℕ) :
    ‖z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)‖ ^ 2 = (‖z‖ ^ 2) ^ n / (n ! : ℝ) := by
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hf.le, ← pow_mul, ← pow_mul,
    mul_comm 2 n]

theorem g75h_mem (z : ℂ) :
    Memℓp (fun n : ℕ => z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  simp_rw [this, Real.rpow_natCast, g75h_coef_norm_sq]
  exact Real.summable_pow_div_factorial _

def g75h_vec (z : ℂ) : Osc.Fock := ⟨_, g75h_mem z⟩

theorem g75h_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) • Osc.fockKet n)
      (g75h_vec z) := by
  have h := lp.hasSum_single (p := 2) (by norm_num) (g75h_vec z)
  convert h using 2 with n
  simp only [Osc.fockKet, QAlgorithms.Papers.Independent.Dependency50.P39.fockKet]
  rw [← lp.single_smul, smul_eq_mul, mul_one]
  rfl

theorem g75h_norm (z : ℂ) : ‖g75h_vec z‖ = Real.exp (Complex.normSq z / 2) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  have : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  have hs : HasSum (fun n : ℕ => (‖z‖ ^ 2) ^ n / (Nat.factorial n : ℝ)) (Real.exp (‖z‖ ^ 2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  simp_rw [this, Real.rpow_natCast]
  change (∑' n : ℕ, ‖z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)‖ ^ 2) ^ (1 / ((2:ℕ):ℝ)) = _
  simp_rw [g75h_coef_norm_sq]
  rw [hs.tsum_eq, ← Real.exp_mul, Complex.normSq_eq_norm_sq]
  congr 1
  push_cast
  ring

theorem g75h_iter (n : ℕ) (y : ℝ) :
    ((iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2))) y : ℝ) : ℂ) =
      iteratedDeriv n (fun u : ℂ => Complex.exp (-(u ^ 2))) (y : ℂ) := by
  induction n generalizing y with
  | zero => simp [Complex.ofReal_exp]
  | succ n ih =>
    have hfR : ContDiff ℝ ⊤ (fun y : ℝ => Real.exp (-(y ^ 2))) := by fun_prop
    have hfC : ContDiff ℂ ⊤ (fun u : ℂ => Complex.exp (-(u ^ 2))) := by fun_prop
    have hdR := hfR.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)
    have hdC := hfC.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)
    have h1 := ((hdR y).hasDerivAt).ofReal_comp
    have h2 := ((hdC (y : ℂ)).hasDerivAt).comp_ofReal
    have he : (fun t : ℝ => ((iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2))) t : ℝ) : ℂ)) =
        (fun t : ℝ => iteratedDeriv n (fun u : ℂ => Complex.exp (-(u ^ 2))) (t : ℂ)) :=
      funext ih
    rw [he] at h1
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact h1.unique h2

theorem g75h_hermite (z : ℂ) (x : ℝ) :
    HasSum (fun n : ℕ =>
      z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * hermiteValue n x)
      ((Real.rpow Real.pi (-(1 : ℝ) / 4) : ℂ) *
        Complex.exp (-(z ^ 2 + (x : ℂ) ^ 2) / 2) *
        Complex.exp (z * (x : ℂ) * (Real.sqrt 2 : ℂ))) := by
  have hFC : Differentiable ℂ (fun u : ℂ => Complex.exp (-(u ^ 2))) := by fun_prop
  set s2 : ℝ := Real.sqrt 2 with hs2def
  set r : ℝ := Real.pi ^ ((1 : ℝ) / 4) with hrdef
  have hs2pos : 0 < s2 := by positivity
  have hrpos : 0 < r := by positivity
  have hs2sq : (s2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, hs2def, Real.sq_sqrt (by norm_num)]; norm_num
  set w : ℂ := -z * (s2 : ℂ) / 2 with hwdef
  have hT := Complex.hasSum_taylorSeries_of_entire hFC (x : ℂ) ((x : ℂ) + w)
  simp only [add_sub_cancel_left] at hT
  have hT2 := hT.mul_left (((r⁻¹ * Real.exp (-(x ^ 2) / 2) * Real.exp (x ^ 2) : ℝ)) : ℂ)
  have hv : (Real.rpow Real.pi (-(1 : ℝ) / 4) : ℂ) *
        Complex.exp (-(z ^ 2 + (x : ℂ) ^ 2) / 2) * Complex.exp (z * (x : ℂ) * (s2 : ℂ)) =
      (((r⁻¹ * Real.exp (-(x ^ 2) / 2) * Real.exp (x ^ 2) : ℝ)) : ℂ) *
        Complex.exp (-(((x : ℂ) + w) ^ 2)) := by
    have hr : Real.rpow Real.pi (-(1 : ℝ) / 4) = r⁻¹ := by
      rw [hrdef, ← Real.rpow_neg Real.pi_pos.le]
      norm_num
    rw [hr]
    push_cast
    simp only [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hwdef]
    linear_combination (z ^ 2 / 4) * hs2sq
  have hf : (fun n : ℕ => z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * hermiteValue n x) =
      (fun n : ℕ => (((r⁻¹ * Real.exp (-(x ^ 2) / 2) * Real.exp (x ^ 2) : ℝ)) : ℂ) *
        ((Nat.factorial n : ℂ)⁻¹ • w ^ n •
          iteratedDeriv n (fun u : ℂ => Complex.exp (-(u ^ 2))) (x : ℂ))) := by
    funext n
    have hw' : w = -z / (s2 : ℂ) := by
      have : (s2 : ℂ) ≠ 0 := by exact_mod_cast hs2pos.ne'
      rw [hwdef]
      field_simp
      linear_combination (-z) * hs2sq
    have hfpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    set sf : ℝ := Real.sqrt (Nat.factorial n : ℝ) with hsfdef
    have hsfpos : 0 < sf := Real.sqrt_pos.mpr hfpos
    have hfact : ((Nat.factorial n : ℕ) : ℂ) = (sf : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hsfdef, Real.sq_sqrt hfpos.le]; norm_cast
    have hsq : Real.sqrt ((2 : ℝ) ^ n * (Nat.factorial n : ℝ) * Real.sqrt Real.pi) =
        s2 ^ n * sf * r := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      have h1 : Real.sqrt ((2 : ℝ) ^ n) = s2 ^ n := by
        rw [show (2 : ℝ) ^ n = (s2 ^ n) ^ 2 by
          rw [← pow_mul, mul_comm, pow_mul, hs2def, Real.sq_sqrt (by norm_num)]]
        exact Real.sqrt_sq (by positivity)
      have h2 : Real.sqrt (Real.sqrt Real.pi) = r := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul Real.pi_pos.le, hrdef]
        norm_num
      rw [h1, h2]
    rw [← g75h_iter n x]
    simp only [hermiteValue, QAlgorithms.Papers.Independent.Renew46.P19.hermiteFunction,
      QAlgorithms.Papers.Independent.Renew46.P19.physicistsHermite, smul_eq_mul]
    rw [hsq, hfact, hw']
    have : (s2 : ℂ) ≠ 0 := by exact_mod_cast hs2pos.ne'
    have : (sf : ℂ) ≠ 0 := by exact_mod_cast hsfpos.ne'
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    push_cast
    rw [div_pow, neg_pow]
    field_simp
    ring
  rw [hf, hv]
  exact hT2

theorem solution (z : ℂ) :
    HasSum (fun n : ℕ =>
      (z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) • Osc.fockKet n)
      (exponentialVector z) ∧
    (∀ x : ℝ, HasSum (fun n : ℕ =>
      z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * hermiteValue n x)
      ((Real.rpow Real.pi (-(1 : ℝ) / 4) : ℂ) *
        Complex.exp (-(z ^ 2 + (x : ℂ) ^ 2) / 2) *
        Complex.exp (z * (x : ℂ) * (Real.sqrt 2 : ℂ)))) ∧
    HasSum (fun n : ℕ =>
      (z ^ n / (Nat.factorial n : ℂ)) • creationPowerVacuum n)
      (creationExponentialVacuum z) ∧
    exponentialVector z = creationExponentialVacuum z ∧
    ‖exponentialVector z‖ = Real.exp (Complex.normSq z / 2) := by
  have hEV : exponentialVector z = g75h_vec z := (g75h_hasSum z).tsum_eq
  have hterm : (fun n : ℕ => (z ^ n / (Nat.factorial n : ℂ)) • creationPowerVacuum n) =
      (fun n : ℕ => (z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) • Osc.fockKet n) := by
    funext n
    rw [creationPowerVacuum, smul_smul]
    congr 1
    have hfpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hsf : ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hfpos).ne'
    have hfact : ((Nat.factorial n : ℕ) : ℂ) = ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hfpos.le]; norm_cast
    rw [hfact]
    field_simp
  have hCV : creationExponentialVacuum z = g75h_vec z := by
    rw [creationExponentialVacuum, hterm]
    exact (g75h_hasSum z).tsum_eq
  refine ⟨hEV ▸ g75h_hasSum z, fun x => g75h_hermite z x, ?_, hEV.trans hCV.symm, ?_⟩
  · rw [hterm, hCV]; exact g75h_hasSum z
  · rw [hEV]; exact g75h_norm z
