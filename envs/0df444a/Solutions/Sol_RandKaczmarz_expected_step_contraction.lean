-- Prove2me | solution 1 for RandKaczmarz.expected_step_contraction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T17:48:05.735986+00:00
-- url     : https://prove2.me/submissions/cca7643a-28c9-4c0f-bb04-834c2c875a8e

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz


variable {m n : ℕ}

/-- `mulVecE A` as a linear map. -/
noncomputable def mulVecL (A : Matrix (Fin m) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) where
  toFun := mulVecE A
  map_add' x y := by ext i; simp [mulVecE_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i; simp [mulVecE_apply, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

lemma norm_mulVecE_sq (A : Matrix (Fin m) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    ‖mulVecE A z‖ ^ 2 = ∑ j, ‖⟪krow A j, z⟫_ℂ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [inner_krow]

lemma sigmaMin_nonneg (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ sigmaMin A :=
  Real.iInf_nonneg fun _ => norm_nonneg _

lemma sigmaMin_mul_le (A : Matrix (Fin m) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    sigmaMin A * ‖z‖ ≤ ‖mulVecE A z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set u : EuclideanSpace ℂ (Fin n) := ((‖z‖ : ℂ)⁻¹) • z
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, norm_norm]; field_simp
  have h1 : sigmaMin A ≤ ‖mulVecE A u‖ :=
    ciInf_le (f := fun z : {z : EuclideanSpace ℂ (Fin n) // ‖z‖ = 1} =>
      ‖mulVecE A (z : EuclideanSpace ℂ (Fin n))‖) ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ ⟨u, hu⟩
  have h2 : mulVecE A u = ((‖z‖ : ℂ)⁻¹) • mulVecE A z := (mulVecL A).map_smul _ z
  rw [h2, norm_smul, norm_inv, Complex.norm_real, norm_norm] at h1
  rwa [le_inv_mul_iff₀ hz', mul_comm] at h1

theorem sum_inner_krow_sq_lower' (A : Matrix (Fin m) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    sigmaMin A ^ 2 * ‖z‖ ^ 2 ≤ ∑ j, ‖⟪krow A j, z⟫_ℂ‖ ^ 2 := by
  rw [← norm_mulVecE_sq, ← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (sigmaMin_nonneg A) (norm_nonneg _))
    (sigmaMin_mul_le A z) 2

lemma sigmaMin_pos (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hA : Function.Injective (mulVecE A)) : 0 < sigmaMin A := by
  obtain ⟨K, hK, hKA⟩ := (LinearMap.injective_iff_antilipschitz (mulVecL A)).mp hA
  have hne : Nonempty {z : EuclideanSpace ℂ (Fin n) // ‖z‖ = 1} :=
    ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩⟩
  have : (K : ℝ)⁻¹ ≤ sigmaMin A := by
    refine le_ciInf fun z => ?_
    have := hKA.le_mul_dist (z : EuclideanSpace ℂ (Fin n)) 0
    simp only [dist_zero_right, z.2, map_zero] at this
    have hK' : (0 : ℝ) < K := hK
    rw [inv_le_iff_one_le_mul₀' hK']
    exact this
  exact lt_of_lt_of_le (inv_pos.mpr (by exact_mod_cast hK)) this

lemma card_mul_sigmaMin_sq_le (A : Matrix (Fin m) (Fin n) ℂ) :
    (n : ℝ) * sigmaMin A ^ 2 ≤ frobSq A := by
  have key : ∀ j : Fin n, sigmaMin A ^ 2 ≤ ∑ i, ‖A i j‖ ^ 2 := fun j => by
    have := sum_inner_krow_sq_lower' A (EuclideanSpace.single j 1)
    simpa [inner_krow, mulVecE_apply, Pi.single_apply] using this
  calc (n : ℝ) * sigmaMin A ^ 2 = ∑ _j : Fin n, sigmaMin A ^ 2 := by simp
    _ ≤ ∑ j : Fin n, ∑ i, ‖A i j‖ ^ 2 := Finset.sum_le_sum fun j _ => key j
    _ = frobSq A := by rw [frobSq, Finset.sum_comm]

theorem sqrt_card_le_scaledCond' (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : Function.Injective (mulVecE A)) :
    Real.sqrt n ≤ scaledCond A := by
  have hs := sigmaMin_pos hn A hA
  rw [scaledCond, le_div_iff₀ hs, ← Real.sqrt_sq hs.le, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.sqrt_le_sqrt (card_mul_sigmaMin_sq_le A)


lemma inner_krow_sol (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (i : Fin m) :
    ⟪krow A i, x⟫_ℂ = b i := by
  rw [inner_krow]; show (A *ᵥ ofLp x) i = b i; rw [hx]

theorem norm_step_sub_sq' (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (i : Fin m) (hi : krow A i ≠ 0) :
    ‖step A b i x₀ - x‖ ^ 2
      = ‖x₀ - x‖ ^ 2 - ‖⟪krow A i, x₀ - x⟫_ℂ‖ ^ 2 / ‖krow A i‖ ^ 2 := by
  have hr : 0 < ‖krow A i‖ := norm_pos_iff.mpr hi
  have hbi : b i - ⟪krow A i, x₀⟫_ℂ = -⟪krow A i, x₀ - x⟫_ℂ := by
    rw [← inner_krow_sol A b x hx i, inner_sub_right]; ring
  have hstep : step A b i x₀ - x
      = (x₀ - x) + ((-⟪krow A i, x₀ - x⟫_ℂ) / ((‖krow A i‖ ^ 2 : ℝ) : ℂ)) • krow A i := by
    rw [step, hbi]; abel
  set a := krow A i
  set s := ⟪a, x₀ - x⟫_ℂ
  rw [hstep, @norm_add_sq ℂ, inner_smul_right, norm_smul]
  have hw : ⟪x₀ - x, a⟫_ℂ = conj s := (inner_conj_symm _ _).symm
  have hc : (-s) / ((‖a‖ ^ 2 : ℝ) : ℂ) * conj s = ((-(‖s‖ ^ 2 / ‖a‖ ^ 2) : ℝ) : ℂ) := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [hw, hc, RCLike.re_to_complex, Complex.ofReal_re, norm_div, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp; ring

lemma scaledCond_sq_inv (A : Matrix (Fin m) (Fin n) ℂ) :
    (scaledCond A ^ 2)⁻¹ = sigmaMin A ^ 2 / frobSq A := by
  rw [scaledCond, div_pow, Real.sq_sqrt (frobSq_nonneg A), inv_div]

lemma rowProb_mul_div (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin m) (t : ℝ)
    (ht : krow A j = 0 → t = 0) :
    rowProb A j * (t / ‖krow A j‖ ^ 2) = t / frobSq A := by
  by_cases hj : krow A j = 0
  · simp [rowProb, hj, ht hj]
  · have : ‖krow A j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hj)
    rw [rowProb, div_mul_div_comm, mul_comm (‖krow A j‖ ^ 2), mul_div_mul_right _ _ this]

theorem expected_inner_krow_sq_lower' (A : Matrix (Fin m) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    (scaledCond A ^ 2)⁻¹ * ‖z‖ ^ 2
      ≤ ∑ j, rowProb A j * (‖⟪krow A j, z⟫_ℂ‖ ^ 2 / ‖krow A j‖ ^ 2) := by
  rw [Finset.sum_congr rfl fun j _ => rowProb_mul_div A j _ fun h => by simp [h],
    ← Finset.sum_div, scaledCond_sq_inv, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (sum_inner_krow_sq_lower' A z) (frobSq_nonneg A)

lemma frobSq_pos (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hA : Function.Injective (mulVecE A)) : 0 < frobSq A := by
  have h1 := sigmaMin_pos hn A hA
  have h2 := card_mul_sigmaMin_sq_le A
  have h3 : (0 : ℝ) < n := by exact_mod_cast hn
  have := mul_pos h3 (pow_pos h1 2)
  linarith

lemma card_le_scaledCond_sq (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hA : Function.Injective (mulVecE A)) : (n : ℝ) ≤ scaledCond A ^ 2 := by
  have h := sqrt_card_le_scaledCond' hn A hA
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this

lemma scaledCond_sq_inv_le_one (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hA : Function.Injective (mulVecE A)) : (scaledCond A ^ 2)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (le_trans (by exact_mod_cast hn) (card_le_scaledCond_sq hn A hA))

lemma step_term (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (i : Fin m) :
    rowProb A i * ‖step A b i x₀ - x‖ ^ 2
      = rowProb A i * ‖x₀ - x‖ ^ 2
        - rowProb A i * (‖⟪krow A i, x₀ - x⟫_ℂ‖ ^ 2 / ‖krow A i‖ ^ 2) := by
  by_cases hi : krow A i = 0
  · simp [rowProb, hi]
  · rw [norm_step_sub_sq' A b x x₀ hx i hi]; ring

theorem expected_step_contraction' (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) :
    ∑ i, rowProb A i * ‖step A b i x₀ - x‖ ^ 2
      ≤ (1 - (scaledCond A ^ 2)⁻¹) * ‖x₀ - x‖ ^ 2 := by
  rw [Finset.sum_congr rfl fun i _ => step_term A b x x₀ hx i, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_rowProb A (frobSq_pos hn A hA).ne']
  have := expected_inner_krow_sq_lower' A (x₀ - x)
  linarith

theorem expErrSq_succ' (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x x₀ : EuclideanSpace ℂ (Fin n)) (k : ℕ) :
    expErrSq A b x (k + 1) x₀ = ∑ i, rowProb A i * expErrSq A b x k (step A b i x₀) := by
  simp only [expErrSq]
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k + 1) => Fin m), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Fin.consEquiv, List.ofFn_succ, pathProb, runSteps, mul_assoc]

theorem randomized_kaczmarz_exp_convergence' (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (hA : Function.Injective (mulVecE A))
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (k : ℕ) :
    expErrSq A b x k x₀ ≤ (1 - (scaledCond A ^ 2)⁻¹) ^ k * ‖x₀ - x‖ ^ 2 := by
  set q := 1 - (scaledCond A ^ 2)⁻¹
  have hq : 0 ≤ q := sub_nonneg.mpr (scaledCond_sq_inv_le_one hn A hA)
  induction k generalizing x₀ with
  | zero => simp
  | succ k ih =>
    rw [expErrSq_succ']
    calc ∑ i, rowProb A i * expErrSq A b x k (step A b i x₀)
        ≤ ∑ i, rowProb A i * (q ^ k * ‖step A b i x₀ - x‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih _) (rowProb_nonneg A i)
      _ = q ^ k * ∑ i, rowProb A i * ‖step A b i x₀ - x‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ q ^ k * (q * ‖x₀ - x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (expected_step_contraction' hn A b hA x x₀ hx)
            (pow_nonneg hq _)
      _ = q ^ (k + 1) * ‖x₀ - x‖ ^ 2 := by ring

theorem expErrSq_le_of_iterations' (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (hkappa : 1 < scaledCond A) (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (hk : 2 * Real.log ε / Real.log (1 - (scaledCond A ^ 2)⁻¹) ≤ (k : ℝ)) :
    expErrSq A b x k x₀ ≤ ε ^ 2 * ‖x₀ - x‖ ^ 2 := by
  set q := 1 - (scaledCond A ^ 2)⁻¹
  have hk2 : 1 < scaledCond A ^ 2 := by nlinarith
  have hq0 : 0 < q := by
    have := inv_lt_one_of_one_lt₀ hk2; simp only [q]; linarith
  have hq1 : q < 1 := by
    have := inv_pos.mpr (lt_trans one_pos hk2); simp only [q]; linarith
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have h1 : (k : ℝ) * Real.log q ≤ 2 * Real.log ε := (div_le_iff_of_neg hlog).mp hk
  have h2 : q ^ k ≤ ε ^ 2 := by
    rw [← Real.log_le_log_iff (pow_pos hq0 _) (pow_pos hε0 _), Real.log_pow, Real.log_pow]
    push_cast; linarith
  exact (randomized_kaczmarz_exp_convergence' hn A b hA x x₀ hx k).trans
    (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))


lemma norm_add_real_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (X Y : E) (t : ℝ) :
    ‖X + (t : ℂ) • Y‖ ^ 2 = ‖X‖ ^ 2 + 2 * (t * Complex.re ⟪X, Y⟫_ℂ) + t ^ 2 * ‖Y‖ ^ 2 := by
  rw [@norm_add_sq ℂ, inner_smul_right, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- If `c ‖z‖² ≤ ‖A z‖²` for all `z` and equality holds at `u`, then the Hermitian form
`⟪A u, A v⟫ - c ⟪u, v⟫` vanishes identically in `v`. -/
lemma form_vanish (A : Matrix (Fin m) (Fin n) ℂ) (c : ℝ)
    (hc : ∀ z, c * ‖z‖ ^ 2 ≤ ‖mulVecE A z‖ ^ 2) (u : EuclideanSpace ℂ (Fin n))
    (hu : ‖mulVecE A u‖ ^ 2 = c * ‖u‖ ^ 2) (v : EuclideanSpace ℂ (Fin n)) :
    ⟪mulVecE A u, mulVecE A v⟫_ℂ = (c : ℂ) * ⟪u, v⟫_ℂ := by
  set ω := ⟪mulVecE A u, mulVecE A v⟫_ℂ - (c : ℂ) * ⟪u, v⟫_ℂ with hω
  obtain ⟨w₀, hw₀⟩ : ∃ w : EuclideanSpace ℂ (Fin n), w = conj ω • v := ⟨_, rfl⟩
  have hAw₀ : mulVecE A w₀ = conj ω • mulVecE A v := by
    rw [hw₀]; exact (mulVecL A).map_smul _ _
  have hAw : ∀ t : ℝ, mulVecE A (u + (t : ℂ) • w₀) = mulVecE A u + (t : ℂ) • mulVecE A w₀ :=
    fun t => by
      show mulVecL A (u + (t : ℂ) • w₀) = mulVecL A u + (t : ℂ) • mulVecL A w₀
      rw [map_add, map_smul]
  have hlin : ⟪mulVecE A u, mulVecE A w₀⟫_ℂ - (c : ℂ) * ⟪u, w₀⟫_ℂ = ((‖ω‖ ^ 2 : ℝ) : ℂ) := by
    have hn : conj ω * ω = ((‖ω‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [hAw₀, hw₀, inner_smul_right, inner_smul_right, ← hn]
    linear_combination (-(conj ω)) * hω
  have hre : Complex.re ⟪mulVecE A u, mulVecE A w₀⟫_ℂ - c * Complex.re ⟪u, w₀⟫_ℂ = ‖ω‖ ^ 2 := by
    have := congrArg Complex.re hlin
    rwa [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at this
  set S := ‖mulVecE A w₀‖ ^ 2 - c * ‖w₀‖ ^ 2
  have hS : 0 ≤ S := sub_nonneg.mpr (hc w₀)
  set N := ‖ω‖ ^ 2
  have key : ∀ t : ℝ, 0 ≤ 2 * t * N + t ^ 2 * S := fun t => by
    have h := hc (u + (t : ℂ) • w₀)
    rw [hAw, norm_add_real_smul_sq, norm_add_real_smul_sq] at h
    have e : 2 * t * N + t ^ 2 * S
        = (‖mulVecE A u‖ ^ 2 + 2 * (t * Complex.re ⟪mulVecE A u, mulVecE A w₀⟫_ℂ)
            + t ^ 2 * ‖mulVecE A w₀‖ ^ 2)
          - c * (‖u‖ ^ 2 + 2 * (t * Complex.re ⟪u, w₀⟫_ℂ) + t ^ 2 * ‖w₀‖ ^ 2) := by
      rw [hu, ← hre]; ring
    rw [e]; linarith
  have hN : N = 0 := by
    have hS1 : 0 < S + 1 := by linarith
    have h1 := key (-N / (S + 1))
    have e : 2 * (-N / (S + 1)) * N + (-N / (S + 1)) ^ 2 * S
        = -(N ^ 2 * (S + 2)) / (S + 1) ^ 2 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity), zero_mul, neg_nonneg] at h1
    have : N ^ 2 ≤ 0 := by nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg N))
  have : ω = 0 := by
    have : ‖ω‖ ^ 2 = 0 := hN
    simpa using this
  rw [hω] at this
  exact sub_eq_zero.mp this

lemma sigmaMin_sq_mul_le (A : Matrix (Fin m) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    sigmaMin A ^ 2 * ‖z‖ ^ 2 ≤ ‖mulVecE A z‖ ^ 2 := by
  rw [norm_mulVecE_sq]; exact sum_inner_krow_sq_lower' A z

/-- A unit vector attaining `σ_min(A)`. -/
lemma exists_min_vec (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 ∧ ‖mulVecE A u‖ = sigmaMin A := by
  have hcont : Continuous fun z => ‖mulVecE A z‖ :=
    (LinearMap.continuous_of_finiteDimensional (mulVecL A)).norm
  have hne : (Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1).Nonempty :=
    ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).exists_isMinOn
    hne hcont.continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  refine ⟨u, hu1, le_antisymm ?_ ?_⟩
  · have : Nonempty {z : EuclideanSpace ℂ (Fin n) // ‖z‖ = 1} := ⟨⟨u, hu1⟩⟩
    exact le_ciInf fun z => isMinOn_iff.mp hmin z (by simp [z.2])
  · exact ciInf_le (f := fun z : {z : EuclideanSpace ℂ (Fin n) // ‖z‖ = 1} =>
      ‖mulVecE A (z : EuclideanSpace ℂ (Fin n))‖) ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ ⟨u, hu1⟩

/-- `⟪A u, A e⟫` expanded over the rows. -/
lemma inner_mulVecE (A : Matrix (Fin m) (Fin n) ℂ) (u e : EuclideanSpace ℂ (Fin n)) :
    ⟪mulVecE A u, mulVecE A e⟫_ℂ = ∑ i, ⟪u, krow A i⟫_ℂ * ⟪krow A i, e⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_krow, ← inner_krow, RCLike.inner_apply, inner_conj_symm, mul_comm]

/-- The general `k`-step expectation of an observable `g`. -/
noncomputable def expF (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (g : EuclideanSpace ℂ (Fin n) → ℝ) (k : ℕ) (x₀ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ p : Fin k → Fin m, pathProb A (List.ofFn p) * g (runSteps A b (List.ofFn p) x₀)

lemma expF_succ (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (g : EuclideanSpace ℂ (Fin n) → ℝ) (k : ℕ) (x₀ : EuclideanSpace ℂ (Fin n)) :
    expF A b g (k + 1) x₀ = ∑ i, rowProb A i * expF A b g k (step A b i x₀) := by
  simp only [expF]
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k + 1) => Fin m), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Fin.consEquiv, List.ofFn_succ, pathProb, runSteps, mul_assoc]

/-- An observable that the one-step average multiplies by `r` is multiplied by `r ^ k`. -/
lemma expF_eigen (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (g : EuclideanSpace ℂ (Fin n) → ℝ) (r : ℝ)
    (hg : ∀ y, ∑ i, rowProb A i * g (step A b i y) = r * g y) (k : ℕ) :
    ∀ y, expF A b g k y = r ^ k * g y := by
  induction k with
  | zero => intro y; simp [expF, pathProb, runSteps]
  | succ k ih =>
    intro y
    rw [expF_succ]
    simp_rw [ih]
    rw [pow_succ, mul_assoc, ← hg y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma pathProb_nonneg (A : Matrix (Fin m) (Fin n) ℂ) : ∀ l, 0 ≤ pathProb A l
  | [] => zero_le_one
  | i :: l => mul_nonneg (rowProb_nonneg A i) (pathProb_nonneg A l)

/-- The coordinate of the error along a right singular vector for `σ_min` contracts by
exactly `1 - κ⁻²` in expectation. -/
lemma coord_step (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (hA : Function.Injective (mulVecE A)) (x : EuclideanSpace ℂ (Fin n))
    (hx : A *ᵥ ofLp x = b) (u : EuclideanSpace ℂ (Fin n))
    (hu : ∀ v, ⟪mulVecE A u, mulVecE A v⟫_ℂ = ((sigmaMin A ^ 2 : ℝ) : ℂ) * ⟪u, v⟫_ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    ∑ i, rowProb A i * Complex.re ⟪u, step A b i y - x⟫_ℂ
      = (1 - (scaledCond A ^ 2)⁻¹) * Complex.re ⟪u, y - x⟫_ℂ := by
  have hF := frobSq_pos hn A hA
  have hF' : (frobSq A : ℂ) ≠ 0 := by exact_mod_cast hF.ne'
  have hterm : ∀ i, ((rowProb A i : ℝ) : ℂ) * ⟪u, step A b i y - x⟫_ℂ
      = (rowProb A i : ℂ) * ⟪u, y - x⟫_ℂ
        - ⟪u, krow A i⟫_ℂ * ⟪krow A i, y - x⟫_ℂ / (frobSq A : ℂ) := by
    intro i
    by_cases hi : krow A i = 0
    · simp [rowProb, hi, step]
    have hr : (‖krow A i‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hi
    have hr' : ((‖krow A i‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
    have hbi : b i - ⟪krow A i, y⟫_ℂ = -⟪krow A i, y - x⟫_ℂ := by
      rw [← inner_krow_sol A b x hx i, inner_sub_right]; ring
    have hstep : step A b i y - x
        = (y - x) + ((-⟪krow A i, y - x⟫_ℂ) / ((‖krow A i‖ ^ 2 : ℝ) : ℂ)) • krow A i := by
      rw [step, hbi]; abel
    rw [hstep, inner_add_right, inner_smul_right, rowProb]
    push_cast
    field_simp
    ring
  have hsum : ∑ i, ((rowProb A i : ℝ) : ℂ) * ⟪u, step A b i y - x⟫_ℂ
      = (((1 - (scaledCond A ^ 2)⁻¹) : ℝ) : ℂ) * ⟪u, y - x⟫_ℂ := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_div, ← inner_mulVecE, hu, scaledCond_sq_inv]
    have h1 : ∑ i, ((rowProb A i : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_sum, sum_rowProb A hF.ne', Complex.ofReal_one]
    rw [h1]
    push_cast
    field_simp
  have := congrArg Complex.re hsum
  rw [Complex.re_sum] at this
  simp only [Complex.re_ofReal_mul] at this
  exact this

lemma sum_pathProb (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (hA : Function.Injective (mulVecE A)) (k : ℕ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ p : Fin k → Fin m, pathProb A (List.ofFn p) = 1 := by
  have := expF_eigen A b (fun _ => 1) 1
    (fun y => by simp [sum_rowProb A (frobSq_pos hn A hA).ne']) k y
  simpa [expF] using this

/-- The weighted Jensen inequality `(∑ w h)² ≤ ∑ w h²` for a probability vector `w`. -/
lemma sq_sum_le_sum_sq {ι : Type*} (s : Finset ι) (w h : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i * h i) ^ 2 ≤ ∑ i ∈ s, w i * h i ^ 2 := by
  set μ := ∑ i ∈ s, w i * h i with hμ
  have h0 : 0 ≤ ∑ i ∈ s, w i * (h i - μ) ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have e : ∑ i ∈ s, w i * (h i - μ) ^ 2
      = ∑ i ∈ s, w i * h i ^ 2 - 2 * μ * (∑ i ∈ s, w i * h i) + μ ^ 2 * ∑ i ∈ s, w i := by
    have ht : ∀ i ∈ s, w i * (h i - μ) ^ 2 = w i * h i ^ 2 - 2 * μ * (w i * h i) + μ ^ 2 * w i :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [e, hw1] at h0
  nlinarith

/-- Core of Theorem 3: with `x₀ = x + u`, `u` a unit vector attaining `σ_min`,
`E Re ⟪u, x_k - x⟫ = (1 - κ⁻²)^k`. -/
lemma lower_core (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (hA : Function.Injective (mulVecE A)) (x : EuclideanSpace ℂ (Fin n))
    (hx : A *ᵥ ofLp x = b) :
    ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 ∧ ∀ k : ℕ,
      ∑ p : Fin k → Fin m, pathProb A (List.ofFn p)
          * Complex.re ⟪u, runSteps A b (List.ofFn p) (x + u) - x⟫_ℂ
        = (1 - (scaledCond A ^ 2)⁻¹) ^ k := by
  obtain ⟨u, hu1, huσ⟩ := exists_min_vec hn A
  have hform := form_vanish A (sigmaMin A ^ 2) (sigmaMin_sq_mul_le A) u
    (by rw [huσ, hu1]; ring)
  refine ⟨u, hu1, fun k => ?_⟩
  have := expF_eigen A b (fun y => Complex.re ⟪u, y - x⟫_ℂ) (1 - (scaledCond A ^ 2)⁻¹)
    (coord_step hn A b hA x hx u (fun v => by rw [hform v])) k (x + u)
  simp only [expF] at this
  rw [this, add_sub_cancel_left, inner_self_eq_norm_sq_to_K, hu1]
  simp

lemma re_inner_le_norm (u e : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1) :
    |Complex.re ⟪u, e⟫_ℂ| ≤ ‖e‖ := by
  calc |Complex.re ⟪u, e⟫_ℂ| ≤ ‖⟪u, e⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖u‖ * ‖e‖ := norm_inner_le_norm u e
    _ = ‖e‖ := by rw [hu, one_mul]

theorem randomized_kaczmarz_lower_bound_norm' (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (x : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) :
    ∃ x₀ : EuclideanSpace ℂ (Fin n), x₀ ≠ x ∧ ∀ k : ℕ, 1 ≤ k →
      (1 - 2 * (k : ℝ) / scaledCond A ^ 2) * ‖x₀ - x‖
        ≤ ∑ p : Fin k → Fin m,
            pathProb A (List.ofFn p) * ‖runSteps A b (List.ofFn p) x₀ - x‖ := by
  obtain ⟨u, hu1, hcore⟩ := lower_core hn A b hA x hx
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  refine ⟨x + u, by simpa using hu0, fun k _ => ?_⟩
  rw [add_sub_cancel_left, hu1, mul_one]
  have hinv0 : 0 ≤ (scaledCond A ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hinv1 := scaledCond_sq_inv_le_one hn A hA
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc 1 - 2 * (k : ℝ) / scaledCond A ^ 2
      ≤ 1 + (k : ℝ) * (-(scaledCond A ^ 2)⁻¹) := by
        rw [div_eq_mul_inv]; nlinarith
    _ ≤ (1 + -(scaledCond A ^ 2)⁻¹) ^ k := one_add_mul_le_pow (by linarith) k
    _ = ∑ p : Fin k → Fin m, pathProb A (List.ofFn p)
          * Complex.re ⟪u, runSteps A b (List.ofFn p) (x + u) - x⟫_ℂ := by
        rw [hcore k, sub_eq_add_neg]
    _ ≤ _ := Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (re_inner_le_norm u _ hu1)) (pathProb_nonneg A _)

theorem randomized_kaczmarz_lower_bound' (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (x : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) :
    ∃ x₀ : EuclideanSpace ℂ (Fin n), x₀ ≠ x ∧ ∀ k : ℕ, 1 ≤ k →
      (1 - 2 * (k : ℝ) / scaledCond A ^ 2) * ‖x₀ - x‖ ^ 2 ≤ expErrSq A b x k x₀ := by
  obtain ⟨u, hu1, hcore⟩ := lower_core hn A b hA x hx
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  refine ⟨x + u, by simpa using hu0, fun k _ => ?_⟩
  rw [add_sub_cancel_left, hu1, one_pow, mul_one]
  have hinv1 := scaledCond_sq_inv_le_one hn A hA
  set h : (Fin k → Fin m) → ℝ :=
    fun p => Complex.re ⟪u, runSteps A b (List.ofFn p) (x + u) - x⟫_ℂ with hh
  calc 1 - 2 * (k : ℝ) / scaledCond A ^ 2
      = 1 + ((2 * k : ℕ) : ℝ) * (-(scaledCond A ^ 2)⁻¹) := by push_cast; ring
    _ ≤ (1 + -(scaledCond A ^ 2)⁻¹) ^ (2 * k) := one_add_mul_le_pow (by linarith) _
    _ = (∑ p : Fin k → Fin m, pathProb A (List.ofFn p) * h p) ^ 2 := by
        rw [hh, hcore k, ← pow_mul, mul_comm k 2, sub_eq_add_neg]
    _ ≤ ∑ p : Fin k → Fin m, pathProb A (List.ofFn p) * h p ^ 2 :=
        sq_sum_le_sum_sq _ _ _ (fun p _ => pathProb_nonneg A _)
          (sum_pathProb hn A b hA k (x + u))
    _ ≤ expErrSq A b x k (x + u) := Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
        (sq_le_sq' (neg_le_of_abs_le (re_inner_le_norm u _ hu1))
          (le_of_abs_le (re_inner_le_norm u _ hu1))) (pathProb_nonneg A _)

lemma norm_mulVecE_single_sq (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    ‖mulVecE A (EuclideanSpace.single j 1)‖ ^ 2 = ∑ i, ‖A i j‖ ^ 2 := by
  rw [norm_mulVecE_sq]; simp [inner_krow, mulVecE_apply, Pi.single_apply]

/-- If `κ(A) = √n`, then `‖A z‖² = σ_min(A)² ‖z‖²` for every `z`. -/
lemma norm_mulVecE_sq_eq_of_scaledCond_eq_sqrt (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hA : Function.Injective (mulVecE A)) (hkappa : scaledCond A = Real.sqrt n)
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖mulVecE A z‖ ^ 2 = sigmaMin A ^ 2 * ‖z‖ ^ 2 := by
  have hσ := sigmaMin_pos hn A hA
  have hF : frobSq A = n * sigmaMin A ^ 2 := by
    have h := congrArg (· ^ 2) hkappa
    simp only [scaledCond, div_pow, Real.sq_sqrt (frobSq_nonneg A),
      Real.sq_sqrt (Nat.cast_nonneg n)] at h
    rw [div_eq_iff (pow_pos hσ 2).ne'] at h
    exact h
  -- every column has squared norm exactly `σ²`
  have hcol : ∀ j : Fin n, ‖mulVecE A (EuclideanSpace.single j 1)‖ ^ 2
      = sigmaMin A ^ 2 * ‖(EuclideanSpace.single j 1 : EuclideanSpace ℂ (Fin n))‖ ^ 2 := by
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), sigmaMin A ^ 2
        ≤ ‖mulVecE A (EuclideanSpace.single j 1)‖ ^ 2 := fun j _ => by
      simpa using sigmaMin_sq_mul_le A (EuclideanSpace.single j 1)
    have hsum : ∑ _j : Fin n, sigmaMin A ^ 2
        = ∑ j : Fin n, ‖mulVecE A (EuclideanSpace.single j 1)‖ ^ 2 := by
      simp only [norm_mulVecE_single_sq]
      rw [Finset.sum_comm, ← frobSq, hF]; simp
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum j (Finset.mem_univ _)
    simp [← this]
  have hform : ∀ j : Fin n, ∀ v, ⟪mulVecE A (EuclideanSpace.single j 1), mulVecE A v⟫_ℂ
      = ((sigmaMin A ^ 2 : ℝ) : ℂ) * ⟪(EuclideanSpace.single j 1 : EuclideanSpace ℂ (Fin n)), v⟫_ℂ :=
    fun j => form_vanish A _ (sigmaMin_sq_mul_le A) _ (hcol j)
  have hz : z = ∑ j, z j • (EuclideanSpace.single j 1 : EuclideanSpace ℂ (Fin n)) := by
    ext i; simp [Pi.single_apply]
  have hAz : mulVecE A z = ∑ j, z j • mulVecE A (EuclideanSpace.single j 1) := by
    conv_lhs => rw [hz]
    show mulVecL A _ = _
    rw [map_sum]; simp only [map_smul]; rfl
  have hinner : ⟪mulVecE A z, mulVecE A z⟫_ℂ = ((sigmaMin A ^ 2 : ℝ) : ℂ) * ⟪z, z⟫_ℂ := by
    nth_rewrite 1 [hAz]
    rw [sum_inner]
    simp only [inner_smul_left, hform, EuclideanSpace.inner_single_left, map_one, one_mul]
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.inner_apply]; ring
  have := congrArg Complex.re hinner
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using this

theorem expErrSq_eq_of_scaledCond_eq_sqrt' (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (hkappa : scaledCond A = Real.sqrt n)
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (k : ℕ) :
    expErrSq A b x k x₀ = (1 - (scaledCond A ^ 2)⁻¹) ^ k * ‖x₀ - x‖ ^ 2 := by
  have hF := frobSq_pos hn A hA
  have hstep : ∀ y, ∑ i, rowProb A i * ‖step A b i y - x‖ ^ 2
      = (1 - (scaledCond A ^ 2)⁻¹) * ‖y - x‖ ^ 2 := fun y => by
    rw [Finset.sum_congr rfl fun i _ => step_term A b x y hx i, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_rowProb A hF.ne',
      Finset.sum_congr rfl fun j _ => rowProb_mul_div A j _ fun h => by simp [h],
      ← Finset.sum_div, ← norm_mulVecE_sq,
      norm_mulVecE_sq_eq_of_scaledCond_eq_sqrt hn A hA hkappa, scaledCond_sq_inv]
    ring
  exact expF_eigen A b (fun y => ‖y - x‖ ^ 2) _ hstep k x₀
end RandKaczmarz

open RandKaczmarz

theorem solution {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) :
    ∑ i, rowProb A i * ‖step A b i x₀ - x‖ ^ 2
      ≤ (1 - (scaledCond A ^ 2)⁻¹) * ‖x₀ - x‖ ^ 2 := expected_step_contraction' hn A b hA x x₀ hx
