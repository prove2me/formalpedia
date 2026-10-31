-- Prove2me | solution 1 for QAlgorithms.Nannicini.gapped_spectral_data
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T15:48:19.140186+00:00
-- url     : https://prove2.me/submissions/adad82ed-aa32-4106-a78c-502e8b2a8c2d

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false

open QAlgorithms

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam γ : ℝ)
    (hγ : 0 < γ) (hA : HasGapAround A lam γ) :
    ∃ P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι,
      (∀ x, P (P x) = P x) ∧
      (∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) ∧
      (∀ x, act A (P x) = (lam : ℂ) • P x) ∧
      (∀ x, P (act A x) = (lam : ℂ) • P x) ∧
      (∀ x, act A (R x) - (lam : ℂ) • R x = x - P x) ∧
      (∀ x, R (act A x) - (lam : ℂ) • R x = x - P x) ∧
      (∀ x, R (P x) = 0) ∧ (∀ x, P (R x) = 0) ∧
      ‖P‖ ≤ 1 ∧ ‖R‖ ≤ 1 / γ ∧ (∃ x, ‖x‖ = 1 ∧ P x = x) := by
  obtain ⟨hH, ⟨k0, hk0, -⟩, hgap⟩ := hA
  set b := hH.eigenvectorBasis with hbdef
  set e : ι → ℝ := hH.eigenvalues with hedef
  set E := EuclideanSpace ℂ ι
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hb : ∀ i, Matrix.toEuclideanLin A (b i) = (e i : ℂ) • b i := by
    intro i
    rw [Matrix.toEuclideanLin_apply, hbdef, hH.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, e]
  have hact : ∀ z j, inner ℂ (b j) (act A z) = (e j : ℂ) * inner ℂ (b j) z := by
    intro z j
    have h1 : act A z = Matrix.toEuclideanLin A z := rfl
    rw [h1, ← hsym (b j) z, hb j, inner_smul_left]
    simp
  -- gap in terms of `hH.eigenvalues`
  have hidx : ∀ j, ascEigenvalues A
      (Fin.rev ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm j)) = e j := by
    intro j
    simp only [ascEigenvalues, dif_pos hH, Fin.rev_rev]
    rfl
  have hg : ∀ j, e j ≠ lam → γ ≤ |e j - lam| := by
    intro j hj
    have := hgap (Fin.rev ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm j))
    rw [hidx j] at this
    exact this hj
  -- diagonal operators in the eigenbasis
  let Dg : (ι → ℂ) → (E →L[ℂ] E) := fun c =>
    ∑ i, c i • (innerSL ℂ (b i)).smulRight (b i)
  have hDg : ∀ c x, Dg c x = ∑ i, (c i * inner ℂ (b i) x) • b i := by
    intro c x
    simp [Dg, mul_smul]
  have hco : ∀ c x j, inner ℂ (b j) (Dg c x) = c j * inner ℂ (b j) x := by
    intro c x j
    rw [hDg, inner_sum]
    simp [inner_smul_right, b.inner_eq_ite]
  have hext : ∀ v w : E, (∀ j, inner ℂ (b j) v = inner ℂ (b j) w) → v = w := by
    intro v w h
    rw [← b.sum_repr' v, ← b.sum_repr' w]
    simp only [h]
  have hnorm : ∀ (c : ι → ℂ) (M : ℝ), 0 ≤ M → (∀ j, ‖c j‖ ≤ M) → ‖Dg c‖ ≤ M := by
    intro c M hM hc
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
    have h2 : ‖Dg c x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
      rw [← b.sum_sq_norm_inner_right, mul_pow, ← b.sum_sq_norm_inner_right, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [hco, norm_mul, mul_pow]
      gcongr
      exact hc j
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  classical
  let p : ι → ℂ := fun j => if e j = lam then 1 else 0
  let a : ι → ℂ := fun j => if e j = lam then 0 else ((e j : ℂ) - lam)⁻¹
  have hne : ∀ j, e j ≠ lam → ((e j : ℂ) - lam) ≠ 0 := by
    intro j hj h
    apply hj
    exact_mod_cast sub_eq_zero.1 h
  refine ⟨Dg p, Dg a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; apply hext; intro j
    rw [hco, hco]; by_cases h : e j = lam <;> simp [p, h]
  · intro x y
    rw [hDg, hDg, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_smul_right, ← inner_conj_symm x (b i)]
    by_cases h : e i = lam <;> simp [p, h, mul_comm]
  · intro x; apply hext; intro j
    rw [hact, hco, inner_smul_right, hco]
    by_cases h : e j = lam <;> simp [p, h]
  · intro x; apply hext; intro j
    rw [hco, hact, inner_smul_right, hco]
    by_cases h : e j = lam <;> simp [p, h] <;> ring
  · intro x; apply hext; intro j
    rw [inner_sub_right, hact, hco, inner_smul_right, hco, inner_sub_right, hco]
    by_cases h : e j = lam
    · simp [a, p, h]
    · simp only [a, p, h, if_false]; field_simp [hne j h]; ring
  · intro x; apply hext; intro j
    rw [inner_sub_right, hco, hact, inner_smul_right, hco, inner_sub_right, hco]
    by_cases h : e j = lam
    · simp [a, p, h]
    · simp only [a, p, h, if_false]; field_simp [hne j h]; ring
  · intro x; apply hext; intro j
    rw [hco, hco]; by_cases h : e j = lam <;> simp [a, p, h]
  · intro x; apply hext; intro j
    rw [hco, hco]; by_cases h : e j = lam <;> simp [a, p, h]
  · refine hnorm p 1 zero_le_one fun j => ?_
    by_cases h : e j = lam <;> simp [p, h]
  · refine hnorm a (1 / γ) (by positivity) fun j => ?_
    by_cases h : e j = lam
    · simp [a, h]; positivity
    · simp only [a, h, if_false, norm_inv]
      have h1 : ‖(e j : ℂ) - lam‖ = |e j - lam| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [h1, one_div]
      exact inv_anti₀ hγ (hg j h)
  · set j0 := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))) (Fin.rev k0)
    have hj0 : e j0 = lam := by
      rw [← hidx j0]; simpa [j0] using hk0
    refine ⟨b j0, b.orthonormal.1 j0, ?_⟩
    apply hext; intro j
    rw [hco]
    by_cases h : j = j0
    · subst h; simp [p, hj0]
    · simp [b.inner_eq_ite, h]
