-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.transfer_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:43:23.749861+00:00
-- url     : https://prove2.me/submissions/811bbe0e-20ec-4760-9996-bea3e264d43d

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem g64b_lp_eq (H omega : Mat I) (p : ℝ≥0∞) :
    lpGenerator H omega p = Matrix.kronecker H 1 - Matrix.kronecker 1
      (supportPower omega (inverseExponent p-1/2) * H *
        supportPower omega (1/2-inverseExponent p))ᵀ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [lpGenerator, Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.transpose_apply]
  congr 1
  · by_cases h : d = b
    · subst h; simp
    · simp [h, Ne.symm h]

theorem g64b_ST (omega : Mat I) (hfaithful : omega.PosDef) (a : ℝ) :
    supportPower omega a * supportPower omega (-a) = 1 := by
  unfold supportPower
  rw [← cfc_mul _ _ omega ((Matrix.finite_real_spectrum).continuousOn _)
    ((Matrix.finite_real_spectrum).continuousOn _)]
  rw [← cfc_one ℝ omega (ha := hfaithful.isHermitian.isSelfAdjoint)]
  apply cfc_congr
  intro x hx
  have hx' : 0 < x := by
    rw [hfaithful.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfaithful.eigenvalues_pos i
  simp only [hx'.ne', if_false, Pi.mul_apply]
  rw [show Real.rpow x (-a) = (Real.rpow x a)⁻¹ from Real.rpow_neg hx'.le a]
  exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hx' a).ne'

theorem g64b_conj_spec (H omega : Mat I) (hfaithful : omega.PosDef) (p : ℝ≥0∞) :
    spectrum ℂ (lpGenerator H omega p) =
      spectrum ℂ (Matrix.kronecker H 1 - Matrix.kronecker 1 Hᵀ) := by
  rw [g64b_lp_eq]
  set S := supportPower omega (inverseExponent p-1/2)
  set T := supportPower omega (1/2-inverseExponent p)
  have hST : S * T = 1 := by
    have := g64b_ST omega hfaithful (inverseExponent p - 1/2)
    rwa [show -(inverseExponent p - 1/2) = 1/2 - inverseExponent p by ring] at this
  have hTS : T * S = 1 := by
    have := g64b_ST omega hfaithful (1/2 - inverseExponent p)
    rwa [show -(1/2 - inverseExponent p) = inverseExponent p - 1/2 by ring] at this
  let u : (Matrix (I × I) (I × I) ℂ)ˣ :=
    { val := Matrix.kronecker 1 Tᵀ, inv := Matrix.kronecker 1 Sᵀ,
      val_inv := by
        simp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, ← Matrix.transpose_mul, hST,
          Matrix.transpose_one, Matrix.one_kronecker_one]
      inv_val := by
        simp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, ← Matrix.transpose_mul, hTS,
          Matrix.transpose_one, Matrix.one_kronecker_one] }
  have : Matrix.kronecker H 1 - Matrix.kronecker 1 (S * H * T)ᵀ =
      (u : Matrix (I × I) (I × I) ℂ) * (Matrix.kronecker H 1 - Matrix.kronecker 1 Hᵀ) *
        ((u⁻¹ : (Matrix (I × I) (I × I) ℂ)ˣ) : Matrix (I × I) (I × I) ℂ) := by
    simp only [u, Units.inv_mk, Units.val_mk, Matrix.mul_sub, Matrix.sub_mul, Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hST,
      Matrix.transpose_one, Matrix.mul_assoc]
  rw [this, spectrum.units_conjugate]

theorem g64b_mem_eig (H : Mat I) (hH : H.IsHermitian) (x : ℝ) :
    x ∈ eigenvalues H ↔ ∃ i, hH.eigenvalues i = x := by
  simp only [eigenvalues, Finset.mem_image, Finset.mem_univ, true_and,
    QAlgorithms.ascEigenvalues, dif_pos hH, Matrix.IsHermitian.eigenvalues]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) k.rev, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).rev, by simp⟩

theorem g64b_spec2 (H : Mat I) (hH : H.IsHermitian) :
    spectrum ℂ (Matrix.kronecker H 1 - Matrix.kronecker 1 Hᵀ) =
      {z | ∃ l ∈ eigenvalues H, ∃ m ∈ eigenvalues H, z = ((l-m : ℝ) : ℂ)} := by
  set U : Mat I := (hH.eigenvectorUnitary : Mat I) with hUdef
  set d : I → ℂ := RCLike.ofReal ∘ hH.eigenvalues with hd
  have hspec : H = U * Matrix.diagonal d * Uᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hUU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hUU' : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  set W : Mat I := (Uᴴ)ᵀ
  set Wh : Mat I := Uᵀ
  have hWW : W * Wh = 1 := by
    simp only [W, Wh]; rw [← Matrix.transpose_mul, hUU, Matrix.transpose_one]
  have hWW' : Wh * W = 1 := by
    simp only [W, Wh]; rw [← Matrix.transpose_mul, hUU', Matrix.transpose_one]
  have hHT : Hᵀ = W * Matrix.diagonal d * Wh := by
    rw [hspec]; simp only [W, Wh, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hDg : Matrix.kronecker (Matrix.diagonal d) (1 : Mat I) -
      Matrix.kronecker (1 : Mat I) (Matrix.diagonal d) =
      Matrix.diagonal (fun x : I × I => d x.1 - d x.2) := by
    ext ⟨a, b⟩ ⟨c, e⟩
    simp only [Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Prod.mk.injEq]
    by_cases h1 : a = c <;> by_cases h2 : b = e <;> simp [h1, h2]
  let u : (Matrix (I × I) (I × I) ℂ)ˣ :=
    { val := Matrix.kronecker U W, inv := Matrix.kronecker Uᴴ Wh,
      val_inv := by
        simp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul, hUU, hWW, Matrix.one_kronecker_one]
      inv_val := by
        simp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul, hUU', hWW', Matrix.one_kronecker_one] }
  have hconj : Matrix.kronecker H 1 - Matrix.kronecker 1 Hᵀ =
      (u : Matrix (I × I) (I × I) ℂ) * Matrix.diagonal (fun x : I × I => d x.1 - d x.2) *
        ((u⁻¹ : (Matrix (I × I) (I × I) ℂ)ˣ) : Matrix (I × I) (I × I) ℂ) := by
    rw [← hDg]
    simp only [u, Units.inv_mk, Units.val_mk, Matrix.mul_sub, Matrix.sub_mul, Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [hUU, hWW, ← hHT, ← hspec]
  rw [hconj, spectrum.units_conjugate, _root_.spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq, g64b_mem_eig H hH]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, by simp [d]⟩
  · rintro ⟨l, ⟨i, rfl⟩, m, ⟨j, rfl⟩, rfl⟩
    exact ⟨⟨i, j⟩, by simp [d]⟩

theorem solution [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    spectrum ℂ (lpGenerator H omega p) = spectrum ℂ (lpGenerator H omega 2) ∧
    spectrum ℂ (lpGenerator H omega 2) =
      {z | ∃ l ∈ eigenvalues H, ∃ m ∈ eigenvalues H, z = ((l-m : ℝ) : ℂ)} := by
  refine ⟨by rw [g64b_conj_spec H omega hfaithful, g64b_conj_spec H omega hfaithful], ?_⟩
  rw [g64b_conj_spec H omega hfaithful]
  exact g64b_spec2 H hH

end
