-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.complex_canonical_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:06:16.687294+00:00
-- url     : https://prove2.me/submissions/6d184167-74be-466d-8927-ac8449d4e421

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4CCC

open Matrix QAlgorithms.Papers.Independent.Claimed50.P41

lemma c_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma star_c : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Complex.conj_ofReal]

lemma omega_def (n : ℕ) : canonicalCoordinateMatrix n =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1) := rfl

lemma omegaH (n : ℕ) : (canonicalCoordinateMatrix n).conjTranspose =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 (-Complex.I • 1) (Complex.I • 1) := by
  rw [omega_def, conjTranspose_smul, star_c, fromBlocks_conjTranspose]
  simp [conjTranspose_smul]

lemma omegaT (n : ℕ) : (canonicalCoordinateMatrix n).transpose =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 (Complex.I • 1) (-Complex.I • 1) := by
  rw [omega_def, transpose_smul, fromBlocks_transpose]
  simp

lemma part1 (n : ℕ) : (canonicalCoordinateMatrix n).conjTranspose * canonicalCoordinateMatrix n = 1 := by
  rw [omegaH, omega_def, smul_mul_smul_comm, c_sq, fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul]
  rw [fromBlocks_smul, ← fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma part2 (n : ℕ) : canonicalCoordinateMatrix n * (canonicalCoordinateMatrix n).conjTranspose = 1 := by
  rw [omegaH, omega_def, smul_mul_smul_comm, c_sq, fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul]
  rw [fromBlocks_smul, ← fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma isigma (n : ℕ) : Complex.I • complexify (sigma n) = Matrix.fromBlocks 0 (Complex.I • 1) (-Complex.I • 1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexify, sigma, Matrix.one_apply] <;> split_ifs <;> simp

lemma csigma (n : ℕ) : complexify (sigma n) = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexify, sigma, Matrix.one_apply] <;> split_ifs <;> simp

lemma part3 (n : ℕ) : canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) *
    (canonicalCoordinateMatrix n).transpose = complexify (sigma n) := by
  rw [isigma, omegaT, omega_def, csigma]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  simp [smul_smul]
  rw [fromBlocks_smul]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma part4 (n : ℕ) : canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) *
    (canonicalCoordinateMatrix n).conjTranspose = sigma3 n := by
  rw [isigma, omegaH, omega_def, sigma3]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  simp [smul_smul]
  rw [fromBlocks_smul]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf


lemma cfb {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    complexify (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

lemma part5 {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    complexForm (Matrix.fromBlocks A B C D) = (1 / 2 : ℂ) • Matrix.fromBlocks
      (complexify (A + D) + Complex.I • complexify (C - B))
      (complexify (A - D) + Complex.I • complexify (B + C))
      (complexify (A - D) - Complex.I • complexify (B + C))
      (complexify (A + D) + Complex.I • complexify (B - C)) := by
  rw [complexForm, omegaH, omega_def, cfb]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  congr 2 <;> ext i j <;> simp [complexify, Matrix.add_apply, Matrix.sub_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

section CCR

variable {n : ℕ}

local notation "e" r => (Pi.single r (1 : ℝ) : Fin n → ℝ)

lemma cre_eq (s : Fin n) (F : (Fin n → ℝ) → ℂ) :
    creationFunction s F = fun q => ((q s : ℂ) * F q + (-1) * fderiv ℝ F q (e s)) / (Real.sqrt 2 : ℂ) := by
  funext q
  simp only [creationFunction, quadratureFunction]
  ring_nf; simp [Complex.I_sq]; ring

lemma ann_eq (s : Fin n) (F : (Fin n → ℝ) → ℂ) :
    annihilationFunction s F = fun q => ((q s : ℂ) * F q + 1 * fderiv ℝ F q (e s)) / (Real.sqrt 2 : ℂ) := by
  funext q
  simp only [annihilationFunction, quadratureFunction]
  ring_nf; simp [Complex.I_sq]

lemma hasFDerivAt_coord (s : Fin n) (q : Fin n → ℝ) :
    HasFDerivAt (fun q : Fin n → ℝ => (q s : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj s)) q :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) s)).hasFDerivAt

lemma D_P (F : (Fin n → ℝ) → ℂ) (hF : Differentiable ℝ F) (r s : Fin n) (q : Fin n → ℝ) :
    fderiv ℝ (fun q => (q s : ℂ) * F q) q (e r) =
      (if r = s then 1 else 0) * F q + (q s : ℂ) * fderiv ℝ F q (e r) := by
  have h : HasFDerivAt (fun q => (q s : ℂ) * F q) _ q := (hasFDerivAt_coord s q).mul (hF q).hasFDerivAt
  rw [h.fderiv]
  simp [Pi.single_apply, eq_comm]
  split_ifs <;> simp [add_comm]

lemma D_lin (u v : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) (hu : DifferentiableAt ℝ u q)
    (hv : DifferentiableAt ℝ v q) (c k : ℂ) (w : Fin n → ℝ) :
    fderiv ℝ (fun q => (u q + c * v q) / k) q w = (fderiv ℝ u q w + c * fderiv ℝ v q w) / k := by
  simp only [div_eq_mul_inv]
  have h : HasFDerivAt (fun q => (u q + c * v q) * k⁻¹) _ q :=
    (HasFDerivAt.add hu.hasFDerivAt (hv.hasFDerivAt.const_mul c)).mul_const k⁻¹
  rw [h.fderiv]
  simp; ring

lemma D_G (F : (Fin n → ℝ) → ℂ) (hF : ContDiff ℝ 2 F) (r s : Fin n) (q : Fin n → ℝ) :
    fderiv ℝ (fun q => fderiv ℝ F q (e s)) q (e r) = fderiv ℝ (fderiv ℝ F) q (e r) (e s) := by
  have hd : Differentiable ℝ (fderiv ℝ F) := (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd q) (differentiableAt_const _)]
  simp

lemma ann_apply (r : Fin n) (g : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) :
    annihilationFunction r g q = ((q r : ℂ) * g q + 1 * fderiv ℝ g q (e r)) / (Real.sqrt 2 : ℂ) := by
  rw [ann_eq]

lemma cre_apply (r : Fin n) (g : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) :
    creationFunction r g q = ((q r : ℂ) * g q + (-1) * fderiv ℝ g q (e r)) / (Real.sqrt 2 : ℂ) := by
  rw [cre_eq]

lemma D_gen (F : (Fin n → ℝ) → ℂ) (hF : ContDiff ℝ 2 F) (c : ℂ) (r s : Fin n) (q : Fin n → ℝ) :
    fderiv ℝ (fun q => ((q s : ℂ) * F q + c * fderiv ℝ F q (e s)) / (Real.sqrt 2 : ℂ)) q (e r) =
      ((if r = s then 1 else 0) * F q + (q s : ℂ) * fderiv ℝ F q (e r) +
        c * fderiv ℝ (fderiv ℝ F) q (e r) (e s)) / (Real.sqrt 2 : ℂ) := by
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hu : DifferentiableAt ℝ (fun q : Fin n → ℝ => (q s : ℂ) * F q) q :=
    (hasFDerivAt_coord s q).differentiableAt.mul (hF1 q)
  have hv : DifferentiableAt ℝ (fun q => fderiv ℝ F q (e s)) q :=
    (hd q).clm_apply (differentiableAt_const _)
  rw [D_lin _ _ q hu hv, D_P F hF1, D_G F hF]

lemma D_cre (F : (Fin n → ℝ) → ℂ) (hF : ContDiff ℝ 2 F) (r s : Fin n) (q : Fin n → ℝ) :
    fderiv ℝ (creationFunction s F) q (e r) =
      ((if r = s then 1 else 0) * F q + (q s : ℂ) * fderiv ℝ F q (e r) +
        (-1) * fderiv ℝ (fderiv ℝ F) q (e r) (e s)) / (Real.sqrt 2 : ℂ) := by
  rw [cre_eq]; exact D_gen F hF _ r s q

lemma D_ann (F : (Fin n → ℝ) → ℂ) (hF : ContDiff ℝ 2 F) (r s : Fin n) (q : Fin n → ℝ) :
    fderiv ℝ (annihilationFunction s F) q (e r) =
      ((if r = s then 1 else 0) * F q + (q s : ℂ) * fderiv ℝ F q (e r) +
        1 * fderiv ℝ (fderiv ℝ F) q (e r) (e s)) / (Real.sqrt 2 : ℂ) := by
  rw [ann_eq]; exact D_gen F hF _ r s q

lemma ccr (F : (Fin n → ℝ) → ℂ) (hF : ContDiff ℝ 2 F) (r s : Fin n) (q : Fin n → ℝ) :
    annihilationFunction r (creationFunction s F) q -
        creationFunction s (annihilationFunction r F) q = kronecker r s * F q ∧
      annihilationFunction r (annihilationFunction s F) q -
        annihilationFunction s (annihilationFunction r F) q = 0 ∧
      creationFunction r (creationFunction s F) q -
        creationFunction s (creationFunction r F) q = 0 := by
  have hsym := (hF.contDiffAt (x := q)).isSymmSndFDerivAt (by simp)
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h] at h2; norm_num at h2
  have hrs := hsym (e r) (e s)
  simp only [ann_apply, cre_apply, D_cre F hF, D_ann F hF, QAlgorithms.Papers.Independent.Claimed50.P41.kronecker]
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : r = s
    · subst h; simp; field_simp; rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 by rw [sq, h2]]; ring
    · have h' : s ≠ r := Ne.symm h
      simp [h, h']; field_simp; linear_combination (-1 : ℂ) * hrs
  · by_cases h : r = s
    · subst h; simp
    · have h' : s ≠ r := Ne.symm h
      simp [h, h']; field_simp; linear_combination (1 : ℂ) * hrs
  · by_cases h : r = s
    · subst h; simp
    · have h' : s ≠ r := Ne.symm h
      simp [h, h']; field_simp; linear_combination (1 : ℂ) * hrs

end CCR

end X4CCC

open QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    (canonicalCoordinateMatrix n).conjTranspose * canonicalCoordinateMatrix n = 1 ∧ canonicalCoordinateMatrix n * (canonicalCoordinateMatrix n).conjTranspose = 1 ∧
    canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) * (canonicalCoordinateMatrix n).transpose = complexify (sigma n) ∧
    canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) * (canonicalCoordinateMatrix n).conjTranspose = sigma3 n ∧
    complexForm (Matrix.fromBlocks A B C D) = (1 / 2 : ℂ) • Matrix.fromBlocks
      (complexify (A + D) + Complex.I • complexify (C - B))
      (complexify (A - D) + Complex.I • complexify (B + C))
      (complexify (A - D) - Complex.I • complexify (B + C))
      (complexify (A + D) + Complex.I • complexify (B - C)) ∧
    (∀ (f : SchwartzMap (Fin n → ℝ) ℂ) (r s : Fin n) (q : Fin n → ℝ),
      annihilationFunction r (creationFunction s f) q -
        creationFunction s (annihilationFunction r f) q = kronecker r s * f q ∧
      annihilationFunction r (annihilationFunction s f) q -
        annihilationFunction s (annihilationFunction r f) q = 0 ∧
      creationFunction r (creationFunction s f) q -
        creationFunction s (creationFunction r f) q = 0) :=
  ⟨X4CCC.part1 n, X4CCC.part2 n, X4CCC.part3 n, X4CCC.part4 n, X4CCC.part5 A B C D,
    fun f r s q => X4CCC.ccr (⇑f) (f.smooth 2) r s q⟩
