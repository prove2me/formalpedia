-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P06.entropy_production_nonadditivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:44:22.323428+00:00
-- url     : https://prove2.me/submissions/72fc90c5-3409-4477-b16e-810c1f1a5936

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06
noncomputable section
open QAlgorithms.Papers.Independent.Gap20.P06
open QAlgorithms
open scoped Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def g73c_Ef : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1/2, 0; 0, 1/2], !![0, 1/2; 1/2, 0], !![1/2, 0; 0, -1/2], !![0, -1/2; 1/2, 0]]

def g73c_Eg : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 0], !![0, 1; 0, 0]]

lemma g73c_Ef_kraus : IsKrausFamily g73c_Ef := by
  unfold IsKrausFamily
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [krausApply, IsKrausFamily, Matrix.sum_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    simp [g73c_Ef, map_ofNat] <;> norm_num

lemma g73c_Eg_kraus : IsKrausFamily g73c_Eg := by
  unfold IsKrausFamily
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [krausApply, IsKrausFamily, Matrix.sum_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    simp [g73c_Eg]

lemma g73c_f_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausApply g73c_Ef X = !![(X 0 0 + X 1 1) / 2, 0; 0, (X 0 0 + X 1 1) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [krausApply, IsKrausFamily, Matrix.sum_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    simp [g73c_Ef, map_ofNat] <;> ring

lemma g73c_g_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausApply g73c_Eg X = !![X 0 0 + X 1 1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [krausApply, IsKrausFamily, Matrix.sum_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    simp [g73c_Eg]

def g73c_psi : EuclideanSpace ℂ (Fin 1 × Fin 2) :=
  WithLp.toLp 2 (fun z => if z.2 = 0 then (1 : ℂ) else 0)

def g73c_s : ℝ := (Real.sqrt 2)⁻¹

lemma g73c_ss : g73c_s * g73c_s = 1 / 2 := by
  unfold g73c_s
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma g73c_ssC : (g73c_s : ℂ) * (g73c_s : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, g73c_ss]; push_cast; ring

def g73c_chi : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun z => if z.1 = z.2 then (g73c_s : ℂ) else 0)

def g73c_rho : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

lemma g73c_A1 : idTensorSuperop (krausApply g73c_Ef) (pureDensity g73c_psi) =
    Matrix.diagonal (fun _ => ((1/2 : ℝ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [idTensorSuperop, Matrix.of_apply, g73c_f_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pureDensity, g73c_psi, Matrix.diagonal_apply]

lemma g73c_A2 : idTensorSuperop (krausApply g73c_Eg ∘ krausApply g73c_Ef) (pureDensity g73c_psi) =
    Matrix.diagonal (fun z => ((if z.2 = 0 then 1 else 0 : ℝ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [idTensorSuperop, Matrix.of_apply, Function.comp_apply, g73c_f_apply, g73c_g_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pureDensity, g73c_psi, Matrix.diagonal_apply] <;> norm_num

lemma g73c_A3 : idTensorSuperop (krausApply g73c_Eg) (pureDensity g73c_chi) =
    Matrix.diagonal (fun z : Fin 2 × Fin 2 => ((if z.2 = 0 then 1/2 else 0 : ℝ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [idTensorSuperop, Matrix.of_apply, g73c_g_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pureDensity, g73c_chi, Matrix.diagonal_apply, g73c_ssC]

lemma g73c_tl_psi : traceLeft (pureDensity g73c_psi) = g73c_rho := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceLeft, pureDensity, g73c_psi, g73c_rho]

lemma g73c_tl_chi : traceLeft (pureDensity g73c_chi) = krausApply g73c_Ef g73c_rho := by
  rw [g73c_f_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceLeft, pureDensity, g73c_chi, g73c_rho, Fin.sum_univ_two, g73c_ssC]
lemma g73c_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g73c_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g73c_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g73c_diag_herm d
  rw [g73c_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g73c_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g73c_trace_cfc_diag]
  simp

lemma g73c_norm_psi : ‖g73c_psi‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [g73c_psi, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g73c_norm_chi : ‖g73c_chi‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have : ‖(g73c_s : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, g73c_ss]
  simp [g73c_chi, Fintype.sum_prod_type, Fin.sum_univ_two, this]
  nlinarith [g73c_ss]

open scoped ComplexOrder in
lemma g73c_rho_dens : IsDensityMatrix g73c_rho := by
  have h : g73c_rho = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g73c_rho]
  rw [h]
  refine ⟨Matrix.PosSemidef.diagonal ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · simp [Matrix.trace_diagonal, Fin.sum_univ_two]

lemma g73c_ent_half : -(((1:ℝ)/2) * Real.logb 2 (1/2)) = 1 / 2 := by
  rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]; norm_num

lemma g73c_E1 : vnEntropy (idTensorSuperop (krausApply g73c_Ef) (pureDensity g73c_psi)) = 1 := by
  rw [g73c_A1, g73c_vn_diag]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g73c_E2 : vnEntropy (idTensorSuperop (krausApply g73c_Eg ∘ krausApply g73c_Ef)
    (pureDensity g73c_psi)) = 0 := by
  rw [g73c_A2, g73c_vn_diag]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g73c_E3 : vnEntropy (idTensorSuperop (krausApply g73c_Eg) (pureDensity g73c_chi)) = 1 := by
  rw [g73c_A3, g73c_vn_diag]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

/-- PDF p.13: overall entropy production may be strictly below both individual
values. Stage two uses a purification chi of the actual intermediate input.
No fixed lower bound on the existential system dimension is imposed. -/
theorem solution :
    ∃ (q r s : ℕ), 0 < q ∧ 0 < r ∧ 0 < s ∧
      ∃ (rho : Matrix (Fin q) (Fin q) ℂ)
        (psi : EuclideanSpace ℂ (Fin r × Fin q))
        (chi : EuclideanSpace ℂ (Fin s × Fin q))
        (f g : Superop (Fin q) (Fin q)),
        IsDensityMatrix rho ∧ ‖psi‖ = 1 ∧ traceLeft (pureDensity psi) = rho ∧
        IsChannel f ∧ IsChannel g ∧ ‖chi‖ = 1 ∧
        traceLeft (pureDensity chi) = f rho ∧
        vnEntropy (idTensorSuperop (g ∘ f) (pureDensity psi)) < vnEntropy (idTensorSuperop f (pureDensity psi)) ∧
        vnEntropy (idTensorSuperop (g ∘ f) (pureDensity psi)) < vnEntropy (idTensorSuperop g (pureDensity chi)) := by
  refine ⟨2, 1, 2, by norm_num, by norm_num, by norm_num, g73c_rho, g73c_psi, g73c_chi,
    krausApply g73c_Ef, krausApply g73c_Eg, g73c_rho_dens, g73c_norm_psi, g73c_tl_psi,
    ⟨4, g73c_Ef, g73c_Ef_kraus, fun _ => rfl⟩, ⟨2, g73c_Eg, g73c_Eg_kraus, fun _ => rfl⟩,
    g73c_norm_chi, g73c_tl_chi, ?_, ?_⟩
  · rw [g73c_E1, g73c_E2]; norm_num
  · rw [g73c_E3, g73c_E2]; norm_num
