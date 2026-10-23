-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.noisy_pure_conditions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:14:59.541985+00:00
-- url     : https://prove2.me/submissions/077c0db7-d847-424a-9d12-d365df94b8cd

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_complete [Nonempty A] (T : UnitaryBasis A K) (i j l m : A) :
    ∑ k, T.matrix k i j * star (T.matrix k l m) =
      if (i, j) = (l, m) then (Fintype.card A : ℂ) else 0 := by
  have hcard : Fintype.card K = Fintype.card (A × A) := by
    rw [T.cardinality, Fintype.card_prod, sq]
  let e : K ≃ A × A := Fintype.equivOfCardEq hcard
  obtain ⟨W, hW⟩ : ∃ W : Matrix (A × A) (A × A) ℂ, ∀ p q, W p q = T.matrix (e.symm q) p.1 p.2 :=
    ⟨Matrix.of fun p q => T.matrix (e.symm q) p.1 p.2, fun _ _ => rfl⟩
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hWW : Wᴴ * W = (Fintype.card A : ℂ) • 1 := by
    ext q q'
    have := T.orthogonal (e.symm q) (e.symm q')
    simp only [trace, diag, mul_apply, conjTranspose_apply] at this
    rw [mul_apply, Matrix.smul_apply, one_apply]
    simp only [conjTranspose_apply, hW, Fintype.sum_prod_type]
    rw [Finset.sum_comm] at this
    rw [this]
    by_cases h : q = q' <;> simp [h, e.symm.injective.eq_iff]
  have h1 : ((Fintype.card A : ℂ)⁻¹ • Wᴴ) * W = 1 := by
    rw [smul_mul_assoc, hWW, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [mul_smul_comm] at h2
  have h3 : W * Wᴴ = (Fintype.card A : ℂ) • 1 := by
    have := congrArg (fun M => (Fintype.card A : ℂ) • M) h2
    simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at this
    exact this
  have := congrFun (congrFun h3 (i, j)) (l, m)
  rw [mul_apply, Matrix.smul_apply, one_apply] at this
  simp only [conjTranspose_apply, hW] at this
  rw [← e.symm.sum_comp (fun k => T.matrix k i j * star (T.matrix k l m))]
  rw [this]
  split_ifs <;> simp


theorem x8_coef_le {U rho : Matrix A A ℂ} (hU : Uᴴ * U = 1) (hrho : IsDensityMatrix rho) :
    ‖(Uᴴ * rho).trace‖ ≤ 1 := by
  set c := (Uᴴ * rho).trace with hc
  by_cases h0 : c = 0
  · rw [h0, norm_zero]; exact zero_le_one
  have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have hcc : c * star c = (‖c‖ : ℂ) * ‖c‖ := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hsn : star (‖c‖ : ℂ) = ‖c‖ := Complex.conj_ofReal _
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = c / ‖c‖ := ⟨_, rfl⟩
  have hzz : star z * z = 1 := by
    rw [hz, star_div₀, hsn, div_mul_div_comm, mul_comm (star c), hcc, div_self (mul_ne_zero hn hn)]
  have hzz2 : z * star z = 1 := by rw [mul_comm]; exact hzz
  obtain ⟨B, hB⟩ : ∃ B : Matrix A A ℂ, B = 1 - z • U := ⟨_, rfl⟩
  have hpsd := hrho.1.conjTranspose_mul_mul_same Bᴴ
  rw [conjTranspose_conjTranspose] at hpsd
  have htr := hpsd.trace_nonneg
  have hcU : (U * rho).trace = star c := by
    rw [hc, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, hrho.1.1.eq,
      trace_mul_comm]
  have hBB : Bᴴ * B = (2 : ℂ) • (1 : Matrix A A ℂ) - star z • Uᴴ - z • U := by
    rw [hB, conjTranspose_sub, conjTranspose_one, conjTranspose_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hU]
    linear_combination (norm := module) hzz2 • (1 : Matrix A A ℂ)
  have e : (B * rho * Bᴴ).trace = 2 - 2 * (‖c‖ : ℂ) := by
    rw [trace_mul_cycle, hBB]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, trace_sub, trace_smul, smul_eq_mul]
    rw [← hc, hcU, hrho.2, hz, star_div₀, hsn, div_mul_eq_mul_div, div_mul_eq_mul_div,
      mul_comm (star c), hcc]
    field_simp
    ring
  rw [e] at htr
  have := (Complex.nonneg_iff.1 htr).1
  simp at this
  linarith

theorem x8_coef_eq (T : K → Matrix A A ℂ) (rho : Matrix A A ℂ) (k : K) :
    basisCoefficient T rho k = ∑ l, ∑ m, star (T k m l) * rho m l := by
  simp [basisCoefficient, trace, mul_apply, conjTranspose_apply]

theorem x8_expand [Nonempty A] (T : UnitaryBasis A K) (rho : Matrix A A ℂ) :
    rho = (Fintype.card A : ℂ)⁻¹ • (∑ k, basisCoefficient T.matrix rho k • T.matrix k) := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, x8_coef_eq, Finset.sum_mul]
  have : ∀ l m, ∑ k, star (T.matrix k m l) * rho m l * T.matrix k i j =
      rho m l * (if (i, j) = (m, l) then (Fintype.card A : ℂ) else 0) := by
    intro l m
    rw [← x8_complete T i j m l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (γ := K)]
  conv_rhs => arg 2; arg 2; ext l; arg 2; ext m; rw [this l m]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp only [if_true]; field_simp
    · intro m _ hm; simp [Ne.symm hm]
    · simp
  · intro l _ hl; refine Finset.sum_eq_zero fun m _ => ?_; simp [Ne.symm hl]
  · simp

theorem x8_parseval [Nonempty A] (T : UnitaryBasis A K) (rho : Matrix A A ℂ) :
    ∑ k, basisCoefficient T.matrix rho k * star (basisCoefficient T.matrix rho k) =
      (Fintype.card A : ℂ) * ∑ l, ∑ m, rho m l * star (rho m l) := by
  simp only [x8_coef_eq, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
  have step : ∀ l m l', ∑ k, ∑ i, star (T.matrix k i l') * rho i l' *
      (T.matrix k m l * star (rho m l)) =
      ∑ i, rho i l' * star (rho m l) * (if (m, l) = (i, l') then (Fintype.card A : ℂ) else 0) := by
    intro l m l'
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← x8_complete T m l i l', Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro m _
  rw [Finset.sum_comm]
  have h2 : ∑ l', ∑ k, ∑ i, star (T.matrix k i l') * rho i l' * (T.matrix k m l * star (rho m l)) =
      ∑ l', ∑ i, rho i l' * star (rho m l) *
        (if (m, l) = (i, l') then (Fintype.card A : ℂ) else 0) :=
    Finset.sum_congr rfl fun l' _ => step l m l'
  rw [h2]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single m]
    · simp; ring
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  · intro l' _ hl; refine Finset.sum_eq_zero fun i _ => ?_; simp [Ne.symm hl]
  · simp

theorem x8_nsq (c : ℂ) : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem x8_scale (T : K → Matrix A A ℂ) (c : K → ℂ) (rho : Matrix A A ℂ) (k k' : K) :
    complementaryChannel (indexedKrausDilation (fun k => c k • T k)) rho k k' =
      c k * star (c k') * complementaryChannel (indexedKrausDilation T) rho k k' := by
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, mul_apply, conjTranspose_apply,
    indexedKrausDilation, Matrix.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl
    fun a _ => ?_
  ring


theorem x8_w (T : UnitaryBasis A K) (psi : EuclideanSpace ℂ A) (j k : K) :
    noisyComplement T.matrix (pureDensity psi) j k = ((Fintype.card A : ℂ)⁻¹)^2 *
      ∑ b, (T.matrix j *ᵥ (fun i => psi i)) b * star ((T.matrix k *ᵥ (fun i => psi i)) b) := by
  unfold noisyComplement
  rw [x8_scale T.matrix (fun _ => (Fintype.card A : ℂ)⁻¹)]
  have : star ((Fintype.card A : ℂ)⁻¹) = (Fintype.card A : ℂ)⁻¹ := by simp
  rw [this, sq]
  congr 1
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, mul_apply, conjTranspose_apply,
    indexedKrausDilation, pureDensity, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
    star_sum, star_mul']
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a _ => ?_
  simp [RCLike.star_def]
  ring

theorem x8_unit_norm (U : Matrix A A ℂ) (hU : Uᴴ * U = 1) (v : A → ℂ) :
    ∑ b, (U *ᵥ v) b * star ((U *ᵥ v) b) = ∑ b, v b * star (v b) := by
  have h1 : ∑ b, (U *ᵥ v) b * star ((U *ᵥ v) b) = star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) := by
    simp only [dotProduct, Pi.star_apply]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have h2 : ∑ b, v b * star (v b) = star v ⬝ᵥ v := by
    simp only [dotProduct, Pi.star_apply]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [h1, h2, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]

theorem x8_g_coef (T : UnitaryBasis A K) (v : A → ℂ) (j k : K) :
    basisCoefficient T.matrix (vecMulVec (T.matrix j *ᵥ v) (star v)) k =
      ∑ b, (T.matrix j *ᵥ v) b * star ((T.matrix k *ᵥ v) b) := by
  rw [x8_coef_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [vecMulVec_apply, mulVec, dotProduct, star_sum, star_mul', Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem x8_main [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (psi : EuclideanSpace ℂ A) (hpsi : IsState psi) :
    let gamma := noisyComplement T.matrix (pureDensity psi)
    gamma.IsHermitian ∧
    ((Fintype.card A : ℂ) • gamma) * ((Fintype.card A : ℂ) • gamma) =
        (Fintype.card A : ℂ) • gamma ∧
    Matrix.rank ((Fintype.card A : ℂ) • gamma) = Fintype.card A ∧
    (∀ k, gamma k k = ((Fintype.card A : ℂ)^2)⁻¹) ∧
    (PhaseClosed T → (∀ j k, ‖gamma j k‖ ≤ ((Fintype.card A : ℝ)^2)⁻¹) ∧
      DoublyStochastic (fun j k => (Fintype.card A : ℝ)^3 * Complex.normSq (gamma j k))) := by
  intro gamma
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = (Fintype.card A : ℂ) := ⟨_, rfl⟩
  have hd : d ≠ 0 := by rw [hd_def]; exact_mod_cast Fintype.card_ne_zero
  obtain ⟨v, hv⟩ : ∃ v : A → ℂ, v = fun i => psi i := ⟨_, rfl⟩
  have hn : ∑ i, v i * star (v i) = 1 := by
    have := EuclideanSpace.norm_eq psi
    rw [hpsi] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h2
    simp only [hv, x8_nsq]
    exact_mod_cast h2.symm
  obtain ⟨M, hM⟩ : ∃ M : Matrix K A ℂ, M = Matrix.of fun j b => (T.matrix j *ᵥ v) b := ⟨_, rfl⟩
  have hγ : gamma = (d⁻¹)^2 • (M * Mᴴ) := by
    ext j k
    rw [Matrix.smul_apply, mul_apply]
    show noisyComplement T.matrix (pureDensity psi) j k = _
    rw [x8_w, ← hd_def, ← hv, hM]
    simp [conjTranspose_apply, smul_eq_mul]
  have hMM : Mᴴ * M = d • (1 : Matrix A A ℂ) := by
    ext a b
    rw [mul_apply, Matrix.smul_apply, one_apply]
    simp only [hM, conjTranspose_apply, of_apply, mulVec, dotProduct, star_sum, star_mul',
      Finset.sum_mul, Finset.mul_sum]
    have key : ∀ e c, ∑ j, star (T.matrix j a c) * star (v c) * (T.matrix j b e * v e) =
        star (v c) * v e * (if (b, e) = (a, c) then d else 0) := by
      intro e c; rw [hd_def, ← x8_complete T b e a c, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [Finset.sum_comm]
    have h2 : ∑ e, ∑ j, ∑ c, star (T.matrix j a c) * star (v c) * (T.matrix j b e * v e) =
        ∑ e, ∑ c, star (v c) * v e * (if (b, e) = (a, c) then d else 0) :=
      Finset.sum_congr rfl fun e _ => by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => key e c
    rw [h2]
    by_cases hab : a = b
    · subst hab
      have : ∀ e, ∑ c, star (v c) * v e * (if (a, e) = (a, c) then d else 0) = star (v e) * v e * d := by
        intro e; rw [Finset.sum_eq_single e]
        · simp
        · intro c _ hc; simp [Ne.symm hc]
        · simp
      simp only [this, if_true, smul_eq_mul, mul_one, ← Finset.sum_mul]
      have : ∑ i, star (v i) * v i = 1 := by rw [← hn]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [this, one_mul]
    · have : ∀ e c, star (v c) * v e * (if (b, e) = (a, c) then d else 0) = 0 := by
        intro e c; simp [Ne.symm hab]
      simp only [this, Finset.sum_const_zero, hab, if_false, smul_zero]
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hdr : d = ((Fintype.card A : ℝ) : ℂ) := by rw [hd_def]; simp
  have hT : ∀ k, T.matrix k * (T.matrix k)ᴴ = 1 := fun k => mul_eq_one_comm.1 (T.unitary k)
  have hg : ∀ j k, gamma j k =
      (d⁻¹)^2 * ∑ b, (T.matrix j *ᵥ v) b * star ((T.matrix k *ᵥ v) b) := by
    intro j k; show noisyComplement T.matrix (pureDensity psi) j k = _
    rw [x8_w, ← hd_def, ← hv]
  have hsd : star (d⁻¹ ^ 2) = d⁻¹ ^ 2 := by rw [hdr]; simp
  have hherm : gamma.IsHermitian := by
    rw [hγ, IsHermitian, conjTranspose_smul, (isHermitian_mul_conjTranspose_self M).eq, hsd]
  have hrow : ∀ j, ∑ k, Complex.normSq (∑ b, (T.matrix j *ᵥ v) b * star ((T.matrix k *ᵥ v) b)) =
      (Fintype.card A : ℝ) := by
    intro j
    have h := x8_parseval T (vecMulVec (T.matrix j *ᵥ v) (star v))
    simp only [x8_g_coef, vecMulVec_apply, Pi.star_apply, star_mul', star_star] at h
    have e : ∑ l, ∑ m, (T.matrix j *ᵥ v) m * star (v l) * (star ((T.matrix j *ᵥ v) m) * v l) =
        (∑ m, (T.matrix j *ᵥ v) m * star ((T.matrix j *ᵥ v) m)) * ∑ l, v l * star (v l) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_; ring
    rw [e, x8_unit_norm _ (T.unitary j), hn, mul_one] at h
    simp only [x8_nsq] at h
    simp only [Complex.normSq_eq_norm_sq]
    simp only [mul_one] at h
    exact_mod_cast h
  have hnγ : ∀ j k, Complex.normSq (gamma j k) = ((Fintype.card A : ℝ) ^ 4)⁻¹ *
      Complex.normSq (∑ b, (T.matrix j *ᵥ v) b * star ((T.matrix k *ᵥ v) b)) := by
    intro j k
    rw [hg, Complex.normSq_mul, hdr, map_pow, map_inv₀, Complex.normSq_ofReal]
    ring
  have hsym : ∀ j k, Complex.normSq (gamma j k) = Complex.normSq (gamma k j) := by
    intro j k
    have := congrFun (congrFun hherm.eq j) k
    rw [conjTranspose_apply] at this
    rw [← this, Complex.star_def, Complex.normSq_conj]
  refine ⟨hherm, ?_, ?_, ?_, ?_⟩
  · rw [← hd_def, hγ, smul_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show M * Mᴴ * (M * Mᴴ) = M * (Mᴴ * M) * Mᴴ by simp [Matrix.mul_assoc], hMM]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
    congr 1; field_simp
  · rw [← hd_def, hγ, smul_smul, rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hd (pow_ne_zero 2 (inv_ne_zero hd)))),
      rank_self_mul_conjTranspose,
      ← rank_conjTranspose_mul_self, hMM,
      rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hd), rank_one]
  · intro k
    rw [hg, x8_unit_norm _ (T.unitary k), hn, mul_one, hd_def, inv_pow]
  · intro _
    refine ⟨fun j k => ?_, ?_, ?_, ?_⟩
    · have hU : ((T.matrix j)ᴴ * T.matrix k)ᴴ * ((T.matrix j)ᴴ * T.matrix k) = 1 := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
          ← Matrix.mul_assoc (T.matrix j), hT j, Matrix.one_mul, T.unitary k]
      have hdens : IsDensityMatrix (pureDensity psi) := by
        refine ⟨?_, ?_⟩
        · have : pureDensity psi = vecMulVec v (star v) := by
            ext i l; simp [pureDensity, vecMulVec, hv]
          rw [this]; exact posSemidef_vecMulVec_self_star v
        · rw [← hn]; simp [trace, pureDensity, hv, RCLike.star_def]
      have hle := x8_coef_le hU hdens
      have heq : (((T.matrix j)ᴴ * T.matrix k)ᴴ * pureDensity psi).trace =
          ∑ b, (T.matrix j *ᵥ v) b * star ((T.matrix k *ᵥ v) b) := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, trace_mul_comm]
        simp only [trace, diag, mul_apply, conjTranspose_apply, pureDensity, of_apply, mulVec,
          dotProduct, Finset.sum_mul, Finset.mul_sum, star_sum, star_mul', hv]
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        simp [RCLike.star_def]; ring
      rw [heq] at hle
      rw [hg, norm_mul, hdr]
      simp only [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card A)]
      rw [inv_pow]
      calc ((Fintype.card A : ℝ) ^ 2)⁻¹ * ‖∑ b, (T.matrix j *ᵥ v) b * star ((T.matrix k *ᵥ v) b)‖
          ≤ ((Fintype.card A : ℝ) ^ 2)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
    · intro j k; exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
    · intro j
      simp only [hnγ, ← Finset.mul_sum, hrow]
      field_simp
    · intro k
      simp only [hsym _ k, hnγ, ← Finset.mul_sum, hrow]
      field_simp

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (psi : EuclideanSpace ℂ A) (hpsi : IsState psi) :
    let gamma := noisyComplement T.matrix (pureDensity psi)
    gamma.IsHermitian ∧
    ((Fintype.card A : ℂ) • gamma) * ((Fintype.card A : ℂ) • gamma) =
        (Fintype.card A : ℂ) • gamma ∧
    Matrix.rank ((Fintype.card A : ℂ) • gamma) = Fintype.card A ∧
    (∀ k, gamma k k = ((Fintype.card A : ℂ)^2)⁻¹) ∧
    (PhaseClosed T → (∀ j k, ‖gamma j k‖ ≤ ((Fintype.card A : ℝ)^2)⁻¹) ∧
      DoublyStochastic (fun j k => (Fintype.card A : ℝ)^3 * Complex.normSq (gamma j k))) :=
  x8_main T psi hpsi
