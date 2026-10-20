-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.amplitudeDampingSpectra
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:33:07.815048+00:00
-- url     : https://prove2.me/submissions/1c8a5490-04a5-4bc1-9d2f-7e19dd6ce8ea

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open Finset
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

lemma g53i_herm_decomp {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    A = ∑ j, (hA.eigenvalues j : ℂ) • pureDensity (hA.eigenvectorBasis j) := by
  conv_lhs => rw [hA.spectral_theorem]
  ext i k
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.sum_apply, Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul,
    Function.comp_apply, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    RCLike.star_def]
  simp [Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

lemma g53i_spec {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    ∃ s : SpectralData A, (∑ j, (s.value j : ℂ)) = A.trace ∧ (∏ j, (s.value j : ℂ)) = A.det := by
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N := Fintype.equivOfCardEq (Fintype.card_fin _)
  let σ : Fin N ≃ Fin N := (finCongr (Fintype.card_fin N)).symm.trans e
  refine ⟨⟨fun j => hA.eigenvalues (σ j), hA.eigenvectorBasis.reindex σ.symm, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    show hA.eigenvalues₀ (e.symm (e _)) ≤ hA.eigenvalues₀ (e.symm (e _))
    simp only [Equiv.symm_apply_apply]
    apply hA.eigenvalues₀_antitone
    simpa using hij
  · conv_lhs => rw [g53i_herm_decomp hA]
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    exact (Equiv.sum_comp σ (fun j => (hA.eigenvalues j : ℂ) • pureDensity (hA.eigenvectorBasis j))).symm
  · rw [hA.trace_eq_sum_eigenvalues]
    simpa using (Equiv.sum_comp σ (fun j => (hA.eigenvalues j : ℂ)))
  · rw [hA.det_eq_prod_eigenvalues]
    exact Equiv.prod_comp σ (fun j => (hA.eigenvalues j : ℂ))
lemma g53i_csq {x : ℝ} (hx : 0 ≤ x) : ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) = x := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma g53i_ad_eq (g : ℝ) (hg : 0 ≤ g) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    amplitudeDamping g X = !![X 0 0 + g * X 1 1, (Real.sqrt (1 - g) : ℂ) * X 0 1;
      (Real.sqrt (1 - g) : ℂ) * X 1 0, (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) * X 1 1] := by
  unfold amplitudeDamping
  have hK0 : (!![1, 0; 0, (Real.sqrt (1 - g) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      !![1, 0; 0, (Real.sqrt (1 - g) : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have hK1 : (!![0, (Real.sqrt g : ℂ); 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      !![0, 0; (Real.sqrt g : ℂ), 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  simp only
  rw [hK0, hK1, Matrix.eta_fin_two X]
  simp only [Matrix.mul_fin_two]
  have := g53i_csq hg
  ext i j; fin_cases i <;> fin_cases j <;> simp [this] <;> ring_nf <;> simp [← Complex.ofReal_pow, Real.sq_sqrt hg] <;> ring

lemma g53i_qi_herm (a f : ℝ) : (qubitInput a f).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qubitInput, Matrix.conjTranspose_apply, ← Complex.exp_conj, Complex.conj_ofReal]

lemma g53i_ad_herm (g : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.IsHermitian) :
    (amplitudeDamping g X).IsHermitian := by
  unfold amplitudeDamping
  exact (Matrix.isHermitian_mul_mul_conjTranspose _ hX).add (Matrix.isHermitian_mul_mul_conjTranspose _ hX)

lemma g53i_two_roots (v : Fin 2 → ℝ) (hv : Antitone v) (d : ℝ)
    (hs : v 0 + v 1 = 1) (hp : v 0 * v 1 = d) :
    v = ![(1 + Real.sqrt (1 - 4 * d)) / 2, (1 - Real.sqrt (1 - 4 * d)) / 2] := by
  have h01 : v 1 ≤ v 0 := hv (by decide)
  have hsq : Real.sqrt (1 - 4 * d) = v 0 - v 1 := by
    rw [show 1 - 4 * d = (v 0 - v 1) ^ 2 by rw [← hp]; nlinarith]
    exact Real.sqrt_sq (by linarith)
  ext j; fin_cases j <;> simp [hsq] <;> linarith

lemma g53i_spec_vals (A : Matrix (Fin 2) (Fin 2) ℂ) (s : SpectralData A) (d : ℝ)
    (ht : (∑ j, (s.value j : ℂ)) = A.trace) (hd : (∏ j, (s.value j : ℂ)) = A.det)
    (htr : A.trace = 1) (hdet : A.det = d) :
    s.value = ![(1 + Real.sqrt (1 - 4 * d)) / 2, (1 - Real.sqrt (1 - 4 * d)) / 2] := by
  apply g53i_two_roots _ s.decreasing
  · rw [htr, Fin.sum_univ_two] at ht; exact_mod_cast ht
  · rw [hdet, Fin.prod_univ_two] at hd; exact_mod_cast hd

lemma g53i_offdiag (a f : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    qubitInput a f 0 1 * qubitInput a f 1 0 = ((a * (1 - a) : ℝ) : ℂ) := by
  simp only [qubitInput, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  have h1 : Complex.exp ((f : ℂ) * Complex.I) * Complex.exp (-(f : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have h2 := g53i_csq (x := a * (1 - a)) (by nlinarith)
  linear_combination (↑√(a * (1 - a)) * ↑√(a * (1 - a)) : ℂ) * h1 + h2

/-- PDF p.3, Lemma 3: both descending output spectra for the two specified inputs.
The complementary input is I−rho0; a and gamma range over [0,1]. -/
theorem solution (a f gamma : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    ∃ (s0 : SpectralData (amplitudeDamping gamma (qubitInput a f)))
      (s1 : SpectralData (amplitudeDamping gamma (1 - qubitInput a f))),
      s0.value = ![(1 + Real.sqrt (1 - 4 * gamma * (1 - gamma) * (1 - a) ^ 2)) / 2,
        (1 - Real.sqrt (1 - 4 * gamma * (1 - gamma) * (1 - a) ^ 2)) / 2] ∧
      s1.value = ![(1 + Real.sqrt (1 - 4 * gamma * (1 - gamma) * a ^ 2)) / 2,
        (1 - Real.sqrt (1 - 4 * gamma * (1 - gamma) * a ^ 2)) / 2] := by
  have hq := g53i_qi_herm a f
  obtain ⟨s0, t0, d0⟩ := g53i_spec (g53i_ad_herm gamma _ hq)
  obtain ⟨s1, t1, d1⟩ := g53i_spec (g53i_ad_herm gamma _ ((Matrix.isHermitian_one).sub hq))
  have hs := g53i_csq (x := 1 - gamma) (by linarith)
  have ho := g53i_offdiag a f ha ha1
  have e00 : qubitInput a f 0 0 = a := by simp [qubitInput]
  have e11 : qubitInput a f 1 1 = ((1 - a : ℝ) : ℂ) := by simp [qubitInput]
  have e1 : 4 * gamma * (1 - gamma) * (1 - a) ^ 2 = 4 * (gamma * (1 - gamma) * (1 - a) ^ 2) := by ring
  have e2 : 4 * gamma * (1 - gamma) * a ^ 2 = 4 * (gamma * (1 - gamma) * a ^ 2) := by ring
  rw [e1, e2]
  refine ⟨s0, s1, ?_, ?_⟩
  · refine g53i_spec_vals _ s0 _ t0 d0 ?_ ?_
    · rw [g53i_ad_eq gamma hg, Matrix.trace_fin_two_of, hs, e00, e11]; push_cast; ring
    · rw [g53i_ad_eq gamma hg, Matrix.det_fin_two_of, e00, e11]
      push_cast at ho hs ⊢
      linear_combination ((a + gamma * (1 - a)) * (1 - a) - qubitInput a f 0 1 * qubitInput a f 1 0) * hs
        - (1 - (gamma:ℂ)) * ho
  · refine g53i_spec_vals _ s1 _ t1 d1 ?_ ?_
    · rw [g53i_ad_eq gamma hg, Matrix.trace_fin_two_of, hs]
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, e00, e11]; push_cast; ring
    · rw [g53i_ad_eq gamma hg, Matrix.det_fin_two_of]
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0:Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1:Fin 2) ≠ 0 by decide), e00, e11]
      push_cast at ho hs ⊢
      linear_combination ((1 - a + gamma * a) * a - qubitInput a f 0 1 * qubitInput a f 1 0) * hs
        - (1 - (gamma:ℂ)) * ho

end
