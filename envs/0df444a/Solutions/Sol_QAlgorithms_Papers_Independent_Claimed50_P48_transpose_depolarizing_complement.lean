-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.transpose_depolarizing_complement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:35:40.258521+00:00
-- url     : https://prove2.me/submissions/cdc425fa-f2ad-488f-b5df-76331a1911d2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

theorem g68l_kc1 (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E := by
  funext rho; ext b b'
  simp only [receiverChannel, traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68l_kc2 (E : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (a b : K) :
    complementaryChannel (indexedKrausDilation E) rho a b = (E a * rho * (E b)ᴴ).trace := by
  simp only [complementaryChannel, traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68l_kc3 (E : K → Matrix B A ℂ) :
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) := by
  funext rho; ext a b
  rw [g68l_kc2]
  simp only [krausApply, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]
theorem g68l_c_sq (d : ℕ) (hd : 2 ≤ d) :
    ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) * ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) =
      (2 * ((d : ℂ) - 1))⁻¹ := by
  have h1 : (0 : ℝ) ≤ 2 * ((d : ℝ) - 1) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt h1]
  push_cast; ring

theorem g68l_rows_eq (d : ℕ) (j : Fin d) :
    antisymmetricRows d j = ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) •
      ((1 - environmentSwap (E := Fin d)) * Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0)) := by
  ext p i
  simp only [antisymmetricRows, Matrix.smul_apply, smul_eq_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, environmentSwap]
  congr 2
  rw [Finset.sum_eq_single (p.2, p.1)]
  · simp [and_comm]
  · intro q _ hq
    have : ¬ p = (q.2, q.1) := fun h => hq (by rw [h])
    simp [this]
  · simp

theorem g68l_swap_herm (d : ℕ) : (1 - environmentSwap (E := Fin d))ᴴ = 1 - environmentSwap (E := Fin d) := by
  have hF : (environmentSwap (E := Fin d))ᴴ = environmentSwap (E := Fin d) := by
    ext ⟨a, b⟩ ⟨c, e⟩
    simp only [Matrix.conjTranspose_apply, environmentSwap, Prod.mk.injEq]
    by_cases h : c = b ∧ e = a
    · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)]; simp
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hF]

theorem g68l_M_sum (d : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j : Fin d, Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) => if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0) *
      rho * (Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) => if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0))ᴴ =
      rho ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext p q
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_and]
  rw [Finset.sum_eq_single q.1 (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  by_cases h : q.2 = p.2
  · simp [h]
  · simp [h, Ne.symm h]

theorem g68l_part1 (d : ℕ) (hd : 2 ≤ d) : antisymmetricComplement d = krausApply (antisymmetricRows d) := by
  funext rho
  simp only [krausApply, g68l_rows_eq]
  set c : ℂ := ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) with hc
  set G := (1 - environmentSwap (E := Fin d))
  have hstar : star c = c := by simp [hc, Complex.conj_ofReal]
  have : ∀ j : Fin d, (c • (G * Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0))) * rho *
      (c • (G * Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0)))ᴴ =
      (c * c) • (G * (Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0) * rho * (Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0))ᴴ) * G) := by
    intro j
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, g68l_swap_herm, hstar]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rfl
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    g68l_M_sum, hc, g68l_c_sq d hd]
  rfl

theorem g68l_part2 (d : ℕ) (j : Fin d) (psi : EuclideanSpace ℂ (Fin d)) (ab : Fin d × Fin d) :
    Matrix.mulVec (antisymmetricRows d j) (fun i => psi i) ab =
        ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) *
          (psi ab.1 * (ket j) ab.2 - (ket j) ab.1 * psi ab.2) := by
  simp only [Matrix.mulVec, dotProduct, antisymmetricRows, ket, mul_sub, sub_mul, Finset.sum_sub_distrib,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, EuclideanSpace.single_apply]
  by_cases h1 : ab.2 = j <;> by_cases h2 : ab.1 = j <;> simp [h1, h2, eq_comm]

theorem g68l_swap_comm (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    environmentSwap (E := Fin d) * (U ⊗ₖ U) = (U ⊗ₖ U) * environmentSwap (E := Fin d) := by
  ext p q
  simp only [Matrix.mul_apply, environmentSwap, Matrix.kroneckerMap_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (p.2, p.1), Finset.sum_eq_single (q.2, q.1)]
  · simp [mul_comm]
  · intro x _ hx; rw [if_neg]; intro h; apply hx; rw [h]
  · simp
  · intro x _ hx; rw [if_neg]; intro h; apply hx; rw [h]
  · simp

theorem g68l_part3 (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    antisymmetricComplement d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) *
          antisymmetricComplement d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ := by
  set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hU : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hk : (V * rho * Vᴴ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) = (V ⊗ₖ V) * (rho ⊗ₖ 1) * (V ⊗ₖ V)ᴴ := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hU]
  have hG : (1 - environmentSwap (E := Fin d)) * (V ⊗ₖ V) = (V ⊗ₖ V) * (1 - environmentSwap (E := Fin d)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, g68l_swap_comm]
  have hG' : (V ⊗ₖ V)ᴴ * (1 - environmentSwap (E := Fin d)) = (1 - environmentSwap (E := Fin d)) * (V ⊗ₖ V)ᴴ := by
    have := congrArg Matrix.conjTranspose hG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, g68l_swap_herm] at this
    exact this
  simp only [antisymmetricComplement, hk, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [← Matrix.mul_assoc, hG]
  simp only [Matrix.mul_assoc, hG']

theorem g68l_part4 (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) :
      wernerHolevo d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        (U : Matrix (Fin d) (Fin d) ℂ).map conj * wernerHolevo d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ).map conj)ᴴ := by
  set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hU : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hU' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h1 : (V.map conj)ᴴ = Vᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  have h2 : (Vᴴ)ᵀ = V.map conj := by ext i j; simp [Matrix.conjTranspose_apply]
  have h3 : V.map conj * Vᵀ = 1 := by
    rw [← h2, ← Matrix.transpose_mul, hU, Matrix.transpose_one]
  have htr : (V * rho * Vᴴ).trace = rho.trace := by
    rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  simp only [wernerHolevo]
  rw [htr]
  simp only [h1, Matrix.transpose_mul, h2, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h3, Matrix.mul_assoc]

theorem g68l_isChannel_of {ι κ K' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype K']
    (E : K' → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (Φ : Superop ι κ) (h : Φ = krausApply E) :
    IsChannel Φ := by
  refine ⟨Fintype.card K', fun i => E ((Fintype.equivFin K').symm i), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Equiv.sum_comp (Fintype.equivFin K').symm (fun k => (E k)ᴴ * E k)
  · rw [h]
    exact (Equiv.sum_comp (Fintype.equivFin K').symm (fun k => E k * rho * (E k)ᴴ)).symm

theorem g68l_row_norm (E : K → Matrix B A ℂ) :
    ∑ b, (rowKraus E b)ᴴ * rowKraus E b = ∑ k, (E k)ᴴ * E k := by
  ext a a'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]
  exact Finset.sum_comm

theorem g68l_row_neg (d : ℕ) : rowKraus (antisymmetricKraus d) = fun b => - antisymmetricRows d b := by
  funext b; ext p a
  simp only [rowKraus, antisymmetricKraus, antisymmetricRows, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.single_apply, smul_eq_mul, Matrix.neg_apply]
  by_cases h1 : p.1 = b <;> by_cases h2 : p.2 = a <;> by_cases h3 : p.2 = b <;> by_cases h4 : p.1 = a <;>
    simp [h1, h2, h3, h4, eq_comm] <;> ring

theorem g68l_kraus_neg {ι κ K' : Type*} [Fintype ι] [Fintype K'] (E : K' → Matrix κ ι ℂ) :
    krausApply (fun k => - E k) = krausApply E := by
  funext rho; simp [krausApply]

theorem g68l_K_norm (d : ℕ) (hd : 2 ≤ d) :
    ∑ k, (antisymmetricKraus d k)ᴴ * antisymmetricKraus d k = 1 := by
  ext a b
  simp only [antisymmetricKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  simp [Matrix.mul_apply, Matrix.single_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ite_and,
    Matrix.one_apply, Finset.mul_sum]
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : ((Real.sqrt (2 * (d : ℝ) - 2) : ℂ))⁻¹ * ((Real.sqrt (2 * (d : ℝ) - 2) : ℂ))⁻¹ =
      (2 * (d : ℂ) - 2)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hne : (d : ℂ) - 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = 1 := by push_cast; linear_combination h
    have := Complex.ofReal_injective (this.trans Complex.ofReal_one.symm); linarith
  have hne2 : 2 * (d : ℂ) - 2 ≠ 0 := by
    intro h; apply hne; linear_combination h / 2
  by_cases h : a = b
  · subst h; simp only [if_true]; rw [hs]; field_simp; ring
  · simp [h, Ne.symm h]

theorem g68l_W_kraus (d : ℕ) (hd : 2 ≤ d) : wernerHolevo d = krausApply (antisymmetricKraus d) := by
  funext rho; ext a b
  simp only [krausApply, antisymmetricKraus, wernerHolevo]
  simp [Matrix.mul_apply, Matrix.single_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ite_and,
    Matrix.one_apply, Finset.mul_sum, Matrix.sum_apply, Fintype.sum_prod_type]
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : ((Real.sqrt (2 * (d : ℝ) - 2) : ℂ))⁻¹ * ((Real.sqrt (2 * (d : ℝ) - 2) : ℂ))⁻¹ =
      (2 * (d : ℂ) - 2)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hne : (d : ℂ) - 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = 1 := by push_cast; linear_combination h
    have := Complex.ofReal_injective (this.trans Complex.ofReal_one.symm); linarith
  have hne2 : 2 * (d : ℂ) - 2 ≠ 0 := by
    intro h; apply hne; linear_combination h / 2
  simp only [← mul_assoc, hs, ← Finset.mul_sum]
  by_cases h : a = b
  · simp only [h, if_true, Matrix.trace, Matrix.diag]; field_simp; ring
  · simp only [h, if_false]; field_simp; ring

/-- Equations (17)–(18), PDF pp.7–8: all d^2 Kraus indices, fixed-basis
transpose, full factor 1/[2(d-1)], and equality on every operator. -/
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    wernerHolevo d = krausApply (antisymmetricKraus d) ∧ IsChannel (wernerHolevo d) ∧
    IsChannel (antisymmetricComplement d) ∧ CPComplementary (wernerHolevo d) (antisymmetricComplement d) ∧
    (∀ rho, complementaryChannel (indexedKrausDilation (antisymmetricKraus d)) rho =
      antisymmetricComplement d rho) := by
  have hrows : krausApply (rowKraus (antisymmetricKraus d)) = krausApply (antisymmetricRows d) := by
    rw [g68l_row_neg]; exact g68l_kraus_neg _
  have hcomp : complementaryChannel (indexedKrausDilation (antisymmetricKraus d)) = antisymmetricComplement d := by
    rw [g68l_kc3, hrows, g68l_part1 d hd]
  refine ⟨g68l_W_kraus d hd, g68l_isChannel_of _ (g68l_K_norm d hd) _ (g68l_W_kraus d hd),
    g68l_isChannel_of (antisymmetricRows d) ?_ _ (g68l_part1 d hd),
    ⟨indexedKrausDilation (antisymmetricKraus d), by rw [g68l_kc1, g68l_W_kraus d hd], hcomp⟩,
    fun rho => by rw [hcomp]⟩
  have := g68l_row_norm (antisymmetricKraus d)
  rw [g68l_K_norm d hd, g68l_row_neg] at this
  simpa using this



end
