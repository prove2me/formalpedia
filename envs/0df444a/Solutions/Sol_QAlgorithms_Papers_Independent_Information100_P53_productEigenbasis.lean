-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.productEigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:35:58.148555+00:00
-- url     : https://prove2.me/submissions/f5aaa87e-fbea-4049-a825-4a7a4f2e427a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open Finset
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

lemma g53i_inner_basis {q : ℕ} (b : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q))) (j k : Fin q) :
    ∑ w, conj (b j w) * b k w = if j = k then 1 else 0 := by
  have h := orthonormal_iff_ite.mp b.orthonormal j k
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← h]; simp [dotProduct, mul_comm]

lemma g53i_eig {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (s : SpectralData A) (k : Fin q) (u : Fin q) :
    ∑ w, A u w * s.basis k w = (s.value k : ℂ) * s.basis k u := by
  have hA : ∀ w, A u w = ∑ m, (s.value m : ℂ) * (s.basis m u * conj (s.basis m w)) := by
    intro w
    have := congrFun (congrFun s.reconstruct u) w
    rw [this]; simp [Matrix.sum_apply, pureDensity]
  simp_rw [hA, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ m, ∑ w, (s.value m : ℂ) * (s.basis m u * conj (s.basis m w)) * s.basis k w =
      (s.value m : ℂ) * s.basis m u * (if m = k then 1 else 0) := by
    intro m
    rw [← g53i_inner_basis s.basis m k, Finset.mul_sum]
    congr 1; ext w; ring
  simp_rw [this]
  simp

/-- PDF pp.4–5, Lemma 4: tensor eigenvalue equation and complete orthonormal
eigenbasis, including reconstruction.
Printed: Section III-C places single-use symbols in D(H_q^{tensor n}).
Changed: single-use states act on H_q. Why: its q spectral labels and the n-factor
construction in Sections II-C and III-C require single-use dimension q. -/
theorem solution {n q : ℕ} (hn : 0 < n) {F : Type*} [Field F] [Fintype F]
    (hq : Fintype.card F = q) (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a)) (s : ∀ a, SpectralData (rho a))
    (x : Fin n → F) :
    (∀ j : Fin n → Fin q, act (productMatrix rho x) (productVector s x j) =
      ((∏ l, (s (x l)).value (j l) : ℝ) : ℂ) • productVector s x j) ∧
    (∃ B : OrthonormalBasis (Fin n → Fin q) ℂ (EuclideanSpace ℂ (Fin n → Fin q)),
      ∀ j, B j = productVector s x j) ∧
    productMatrix rho x = ∑ j : Fin n → Fin q,
      (((∏ l, (s (x l)).value (j l) : ℝ) : ℂ) • pureDensity (productVector s x j)) := by
  have hon : Orthonormal ℂ (productVector s x) := by
    rw [orthonormal_iff_ite]
    intro j k
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, productVector, Pi.star_apply, RCLike.star_def, map_prod]
    have : ∀ u : Fin n → Fin q, (∏ l, (s (x l)).basis (k l) (u l)) * ∏ l, conj ((s (x l)).basis (j l) (u l))
        = ∏ l, (conj ((s (x l)).basis (j l) (u l)) * (s (x l)).basis (k l) (u l)) := by
      intro u; rw [← Finset.prod_mul_distrib]; congr 1; ext l; ring
    try simp only [WithLp.ofLp_toLp]
    simp_rw [this]
    rw [← Fintype.prod_sum (fun l w => conj ((s (x l)).basis (j l) w) * (s (x l)).basis (k l) w)]
    simp_rw [g53i_inner_basis]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [if_neg hjk]
      obtain ⟨l, hl⟩ := Function.ne_iff.mp hjk
      exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    ext u
    simp only [act, productMatrix, productVector, Matrix.mulVec, dotProduct, PiLp.smul_apply,
      WithLp.ofLp_toLp, smul_eq_mul, Complex.ofReal_prod]
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun l w => rho (x l) (u l) w * (s (x l)).basis (j l) w)]
    simp_rw [g53i_eig]
  · haveI : Nonempty (Fin q) := ⟨⟨0, by rw [← hq]; exact Fintype.card_pos⟩⟩
    have hcard : Fintype.card (Fin n → Fin q) = Module.finrank ℂ (EuclideanSpace ℂ (Fin n → Fin q)) := by
      simp
    refine ⟨(basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis (by simpa using hon), ?_⟩
    intro j; simp
  · ext u v
    simp only [productMatrix, Matrix.sum_apply, Matrix.smul_apply, pureDensity, Matrix.of_apply,
      productVector, smul_eq_mul, Complex.ofReal_prod, map_prod]
    have hr : ∀ l, rho (x l) (u l) (v l) = ∑ k, (s (x l)).value k * ((s (x l)).basis k (u l) *
        conj ((s (x l)).basis k (v l))) := by
      intro l
      conv_lhs => rw [(s (x l)).reconstruct]
      simp [Matrix.sum_apply, pureDensity]
    simp_rw [hr]
    rw [Fintype.prod_sum]
    congr 1; ext j
    try simp only [WithLp.ofLp_toLp]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

end
