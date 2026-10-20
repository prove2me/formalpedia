-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.boundDominance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:56:12.494064+00:00
-- url     : https://prove2.me/submissions/f40da93d-9170-48dd-a01e-9c747472c559

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

open Finset

lemma g53e_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g53e_conj_eig {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma g53e_posPart_aux {n : Type} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma g53e_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53e_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53e_posPart_le {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g53e_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g53e_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g53e_posPart_aux lam hA hB hu hD

lemma g53e_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma g53e_negPart_eq {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]


lemma g53e_pairs {M : ℕ} (p : Fin M → ℝ) (hs : ∑ i, p i = 1) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (p i + p j) = (M : ℝ) - 1 := by
  simp only [Finset.sum_filter]
  have h1 : ∑ i : Fin M, ∑ j : Fin M, (if i < j then p i + p j else 0) =
      ∑ i : Fin M, ∑ j : Fin M, (if j < i then p i + p j else 0) := by
    rw [Finset.sum_comm]; simp only [add_comm]
  have h2 : ∑ i : Fin M, ∑ j : Fin M, ((if i < j then p i + p j else 0) +
      (if j < i then p i + p j else 0)) =
      ∑ i : Fin M, ∑ j : Fin M, (p i + p j) - ∑ i : Fin M, (p i + p i) := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [lt_irrefl, if_false, add_zero, zero_add]
    rw [add_comm]; congr 1
    apply Finset.sum_congr rfl; intro j hj
    have := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne this with h | h
    · simp [h, not_lt_of_gt h]
    · simp [h, not_lt_of_gt h]
  simp only [Finset.sum_add_distrib] at h2
  rw [← h1] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hs] at h2
  linarith

lemma g53e_tn_le {n : Type} [Fintype n] [DecidableEq n] (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (A B : Matrix n n ℂ) (hA : QAlgorithms.IsDensityMatrix A) (hB : QAlgorithms.IsDensityMatrix B) :
    QAlgorithms.traceNorm ((a : ℂ) • A - (b : ℂ) • B) ≤ a + b := by
  have hA' : ((a : ℂ) • A).PosSemidef := hA.1.smul (by exact_mod_cast ha)
  have hB' : ((b : ℂ) • B).PosSemidef := hB.1.smul (by exact_mod_cast hb)
  have hY : ((a : ℂ) • A - (b : ℂ) • B).IsHermitian := hA'.isHermitian.sub hB'.isHermitian
  rw [g53e_traceNorm_herm hY, g53e_negPart_eq]
  have h1 := g53e_posPart_le hY hA' hB' rfl
  have h2 := g53e_posPart_le hY.neg hB' hA' (by abel)
  have ta : ((a : ℂ) • A).trace.re = a := by simp [Matrix.trace_smul, hA.2]
  have tb : ((b : ℂ) • B).trace.re = b := by simp [Matrix.trace_smul, hB.2]
  linarith

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

/-- PDF p.4, comparison after Corollary 2 and footnote 2: each new numerical lower
bound dominates its older counterpart; the pair-sum bound is a conclusion, not an assumption. -/
theorem solution {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    (1 / 2 - traceSum p rho / (2 * ((M : ℝ) - 1)) ≤
      1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ)) ∧
    (1 / 2 - fidelitySum p rho / (2 * ((M : ℝ) - 1)) ≤
      1 - 1 / (M : ℝ) - fidelitySum p rho / (M : ℝ)) := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have key : ∀ S : ℝ, S ≤ (M : ℝ) - 1 →
      1 / 2 - S / (2 * ((M : ℝ) - 1)) ≤ 1 - 1 / (M : ℝ) - S / (M : ℝ) := by
    intro S hS
    have h1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    have h0 : (0 : ℝ) < M := by linarith
    rw [← sub_nonneg]
    have : 1 - 1 / (M : ℝ) - S / M - (1 / 2 - S / (2 * (M - 1))) =
        ((M : ℝ) - 2) * ((M - 1) - S) / (2 * M * (M - 1)) := by
      field_simp; ring
    rw [this]
    apply div_nonneg
    · apply mul_nonneg <;> linarith
    · positivity
  refine ⟨key _ ?_, key _ ?_⟩
  · rw [← g53e_pairs p hp.2]
    unfold traceSum pairSum
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact g53e_tn_le _ _ (hp.1 i) (hp.1 j) _ _ (hrho i) (hrho j)
  · rw [← g53e_pairs p hp.2]
    unfold fidelitySum pairSum
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have hi := hp.1 i
    have hj := hp.1 j
    have hF : 0 ≤ fidelity (rho i) (rho j) := by unfold fidelity; positivity
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [mul_nonneg hi hj]

end
