-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.proposition1_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:06:22.999717+00:00
-- url     : https://prove2.me/submissions/eed13862-3d8a-4787-af96-d0a60d5293b0

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


lemma g58a_pauli_compl (a b a' b' : Bool) :
    ∑ p : Fin 4, singlePauli p a b * conj (singlePauli p a' b') =
      if a = a' ∧ b = b' then 2 else 0 := by
  rw [Fin.sum_univ_four]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [singlePauli, pauliX, pauliY, pauliZ] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

lemma g58a_pauli_herm (p : Fin 4) (a b : Bool) : star (singlePauli p a b) = singlePauli p b a := by
  fin_cases p <;> cases a <;> cases b <;> simp [singlePauli, pauliX, pauliY, pauliZ]

lemma g58a_word_apply {n : ℕ} (P : Fin n → Fin 4) (y x : Fin n → Bool) :
    wordMatrix P y x = ∏ i, singlePauli (P i) (y i) (x i) := rfl

lemma g58a_word_compl {n : ℕ} (y x y' x' : Fin n → Bool) :
    ∑ P : Fin n → Fin 4, wordMatrix P y x * conj (wordMatrix P y' x') =
      if y = y' ∧ x = x' then (2 : ℂ) ^ n else 0 := by
  simp only [g58a_word_apply, map_prod]
  simp only [← Finset.prod_mul_distrib]
  have : ∏ i, ∑ p : Fin 4, singlePauli p (y i) (x i) * conj (singlePauli p (y' i) (x' i)) =
      ∑ P : Fin n → Fin 4, ∏ i, singlePauli (P i) (y i) (x i) * conj (singlePauli (P i) (y' i) (x' i)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [← this]
  simp only [g58a_pauli_compl]
  by_cases h : y = y' ∧ x = x'
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    have : ∃ i, ¬ (y i = y' i ∧ x i = x' i) := by
      by_contra hc; push Not at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma g58a_word_herm {n : ℕ} (P : Fin n → Fin 4) : (wordMatrix P)ᴴ = wordMatrix P := by
  ext x y
  rw [Matrix.conjTranspose_apply, g58a_word_apply, g58a_word_apply]
  rw [show star (∏ i, singlePauli (P i) (y i) (x i)) = starRingEnd ℂ (∏ i, singlePauli (P i) (y i) (x i))
    from rfl, map_prod]
  exact Finset.prod_congr rfl fun i _ => g58a_pauli_herm _ _ _

lemma g58a_tr {n : ℕ} (P : Fin n → Fin 4) (H : Matrix (Qubits n) (Qubits n) ℂ) :
    (wordMatrix P * H).trace = ∑ z : Qubits n × Qubits n, wordMatrix P z.1 z.2 * H z.2 z.1 := by
  rw [Fintype.sum_prod_type]; rfl

lemma g58a_parseval {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) (hH : H.IsHermitian) :
    ∑ P : Fin n → Fin 4, coefficient H P ^ 2 =
      (∑ z : Qubits n × Qubits n, ‖H z.2 z.1‖ ^ 2) / (2 : ℝ) ^ n := by
  have hreal : ∀ P, ((wordMatrix P * H).trace.re : ℂ) = (wordMatrix P * H).trace := by
    intro P
    have : star (wordMatrix P * H).trace = (wordMatrix P * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.eq, g58a_word_herm,
        Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.mp this
  have hsq : ∀ P, coefficient H P ^ 2 =
      ((wordMatrix P * H).trace * conj (wordMatrix P * H).trace).re / ((2 : ℝ) ^ n) ^ 2 := by
    intro P
    unfold coefficient
    rw [Fintype.card_fin, div_pow, ← hreal P, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring_nf
    rw [mul_comm]
    congr
    all_goals exact Subsingleton.elim _ _
  simp only [hsq, ← Finset.sum_div, ← Complex.re_sum]
  have key : ∑ P : Fin n → Fin 4, (wordMatrix P * H).trace * conj (wordMatrix P * H).trace =
      (2 : ℂ) ^ n * ∑ z : Qubits n × Qubits n, H z.2 z.1 * conj (H z.2 z.1) := by
    simp only [g58a_tr, map_sum, map_mul, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ z z' : Qubits n × Qubits n, ∑ P : Fin n → Fin 4,
        wordMatrix P z.1 z.2 * H z.2 z.1 * (conj (wordMatrix P z'.1 z'.2) * conj (H z'.2 z'.1)) =
        (if z = z' then (2 : ℂ) ^ n else 0) * (H z.2 z.1 * conj (H z'.2 z'.1)) := by
      intro z z'
      have := g58a_word_compl z.1 z.2 z'.1 z'.2
      have h' : (if z.1 = z'.1 ∧ z.2 = z'.2 then (2:ℂ)^n else 0) = if z = z' then 2^n else 0 := by
        simp [Prod.ext_iff]
      rw [h'] at this
      rw [← this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [Finset.sum_comm (γ := Fin n → Fin 4), this, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
  rw [key]
  have hn : ∀ z : Qubits n × Qubits n, H z.2 z.1 * conj (H z.2 z.1) = ((‖H z.2 z.1‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hn, ← Complex.ofReal_sum, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

lemma g58a_col {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) (y : Qubits n) :
    ∑ x, ‖H x y‖ ^ 2 ≤ specNorm H ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec H (EuclideanSpace.single y 1)
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  have h0 : 0 ≤ ‖(EuclideanSpace.equiv (Qubits n) ℂ).symm (H *ᵥ (EuclideanSpace.single y (1 : ℂ)))‖ :=
    norm_nonneg _
  have h2 := pow_le_pow_left₀ h0 h 2
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
  have e : ∀ x, ((EuclideanSpace.equiv (Qubits n) ℂ).symm
      (H *ᵥ (EuclideanSpace.single y (1 : ℂ)))).ofLp x = H x y := by
    intro x; simp [Matrix.mulVec, dotProduct]
  simp only [e] at h2
  exact h2

theorem solution (n : ℕ) (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) :
    frobNorm H / Real.sqrt ((2 : ℝ) ^ n) = pauliNorm 2 H ∧
      pauliNorm 2 H ≤ specNorm H := by
  set F := ∑ z : Qubits n × Qubits n, ‖H z.2 z.1‖ ^ 2 with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfrob : frobNorm H = Real.sqrt F := by
    unfold frobNorm
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    rw [hF, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Real.rpow_two]
  have hpauli : pauliNorm 2 H = Real.sqrt (F / 2 ^ n) := by
    unfold pauliNorm
    rw [Real.sqrt_eq_rpow, ← g58a_parseval H hH]
    congr 1
    refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun P _ => ?_
    rw [Real.rpow_eq_pow, Real.rpow_two, sq_abs]
  refine ⟨?_, ?_⟩
  · rw [hfrob, hpauli, Real.sqrt_div' _ (by positivity)]
  · rw [hpauli]
    have hs : 0 ≤ specNorm H := norm_nonneg _
    rw [← Real.sqrt_sq hs]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have : F ≤ ∑ y : Qubits n, specNorm H ^ 2 := by
      rw [hF, Fintype.sum_prod_type]
      exact Finset.sum_le_sum fun y _ => g58a_col H y
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    simp only [Qubits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    push_cast at this
    linarith

end
