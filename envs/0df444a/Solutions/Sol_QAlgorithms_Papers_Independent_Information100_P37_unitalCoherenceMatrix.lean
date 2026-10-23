-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.unitalCoherenceMatrix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:25:07.268954+00:00
-- url     : https://prove2.me/submissions/b874af27-879e-48bb-a574-2cca333a6663

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7U_frob_sq {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    frobNorm X ^ 2 = ∑ i, ∑ j, Complex.normSq (X i j) := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [Complex.sq_norm]

lemma X7U_normSq_re (z : ℂ) : Complex.normSq z = (conj z * z).re := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma X7U_kraus_lin {ι K α : Type*} [Fintype ι] [Fintype K] [Fintype α]
    (A : K → Matrix ι ι ℂ) (f : α → ℂ) (X : α → Matrix ι ι ℂ) :
    krausApply A (∑ a, f a • X a) = ∑ a, f a • krausApply A (X a) := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]

lemma X7U_diag_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℂ) :
    Matrix.diagonal p = ∑ i, p i • Matrix.single i i (1 : ℂ) := by
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : a = b
  · subst h; simp [Finset.sum_ite_eq']
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    aesop

lemma X7U_offDiag_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : α → ℂ) (X : α → Matrix ι ι ℂ) :
    offDiagonal (∑ a, f a • X a) = ∑ a, f a • offDiagonal (X a) := by
  ext l m
  simp only [offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

lemma X7U_E_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (q : ι → ℂ) :
    offDiagonal (E (Matrix.diagonal q)) = ∑ i, q i • channelOutput E i := by
  obtain ⟨m, A, -, hA⟩ := hE
  rw [hA, X7U_diag_eq, X7U_kraus_lin, X7U_offDiag_sum]
  simp [channelOutput, hA]

lemma X7U_kraus_single {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (A : K → Matrix ι ι ℂ) (i l m : ι) :
    krausApply A (Matrix.single i i 1) l m = ∑ k, A k l i * conj (A k m i) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma X7U_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (i l m : ι) : conj (channelOutput E i l m) = channelOutput E i m l := by
  obtain ⟨n, A, -, hA⟩ := hE
  simp only [channelOutput, offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag,
    hA, X7U_kraus_single]
  by_cases h : l = m
  · subst h; simp
  · simp [h, Ne.symm h, map_sum, mul_comm]

lemma X7U_resp {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (i j : ι) : channelResponse E i j =
      ∑ l, ∑ m, (conj (channelOutput E i l m) * channelOutput E j l m).re := by
  simp only [channelResponse, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum,
    X7U_herm E hE]
  rw [Finset.sum_comm]

lemma X7U_normSq_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) (z : ι → ℂ) :
    Complex.normSq (∑ i, (x i : ℂ) * z i) = ∑ i, ∑ j, x i * x j * (conj (z i) * z j).re := by
  rw [X7U_normSq_re, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  rw [show (x i : ℂ) * conj (z i) * ((x j : ℂ) * z j) =
    ((x i * x j : ℝ) : ℂ) * (conj (z i) * z j) by push_cast; ring, Complex.re_ofReal_mul]

lemma X7U_swap3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma X7U_key {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (x : ι → ℝ) : quadratic (channelResponse E) x =
      ∑ l, ∑ m, Complex.normSq (∑ i, (x i : ℂ) * channelOutput E i l m) := by
  simp only [quadratic, X7U_resp E hE, X7U_normSq_sum, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => X7U_swap3 _).trans ?_
  refine (X7U_swap3 _).trans ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (E : Superop ι ι)
    (hE : IsChannel E) (hu : E 1 = 1) :
    (∀ p, IsPopulation p → generated E p = quadratic (channelResponse E) p) ∧
    (channelResponse E).IsSymm ∧ (channelResponse E).PosSemidef ∧
    (channelResponse E).mulVec (fun _ => 1) = 0 := by
  have hsymm : ∀ i j, channelResponse E i j = channelResponse E j i := by
    intro i j
    simp only [channelResponse]
    rw [Matrix.trace_mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _
    rw [X7U_key E hE]
    have h := X7U_E_diag E hE (fun i => (p i : ℂ))
    have hc : generated E p = ∑ l, ∑ m, Complex.normSq
        (offDiagonal (E (inputDensity p)) l m) := by
      simp only [generated, coherence, offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply,
        Matrix.diag]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      split_ifs with h
      · subst h; simp
      · simp
    rw [hc, inputDensity, h]
    simp [Matrix.sum_apply]
  · ext i j; exact hsymm j i
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext i j; simp [hsymm j i]
    · have := X7U_key E hE x
      simp only [quadratic] at this
      simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, ← mul_assoc]
      rw [this]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · have h0 : ∑ j, channelOutput E j = 0 := by
      have := X7U_E_diag E hE (fun _ => 1)
      simp only [Matrix.diagonal_one, hu, one_smul] at this
      rw [← this]
      ext l m; simp [offDiagonal, Matrix.one_apply]
    ext i
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply, channelResponse,
      ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, h0]
    simp
