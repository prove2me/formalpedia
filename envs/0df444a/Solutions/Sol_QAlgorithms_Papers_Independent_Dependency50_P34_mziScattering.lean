-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P34.mziScattering
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:44:02.470863+00:00
-- url     : https://prove2.me/submissions/6418a040-adaf-438a-b970-6a79bc495fd1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34

noncomputable section

open scoped Matrix
open QAlgorithms.Papers.Independent.Dependency50.P34

lemma x4mzi_entries (a b c d : ℂ) (h : !![a, b; c, d] ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖c‖ = ‖b‖ ∧ ‖d‖ = ‖a‖ ∧ ‖b‖ ^ 2 + ‖d‖ ^ 2 = 1 ∧ star b * a + c * star d = 0 := by
  have h1 := Matrix.mem_unitaryGroup_iff'.1 h
  have h2 := Matrix.mem_unitaryGroup_iff.1 h
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e10 := congrFun (congrFun h1 1) 0
  have f00 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at e00 e11 e10 f00
  have na : (‖a‖ ^ 2 : ℝ) = Complex.normSq a := (Complex.normSq_eq_norm_sq a).symm
  have nb : (‖b‖ ^ 2 : ℝ) = Complex.normSq b := (Complex.normSq_eq_norm_sq b).symm
  have nc : (‖c‖ ^ 2 : ℝ) = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
  have nd : (‖d‖ ^ 2 : ℝ) = Complex.normSq d := (Complex.normSq_eq_norm_sq d).symm
  have r00 : Complex.normSq a + Complex.normSq c = 1 := by
    have := congrArg Complex.re e00; simpa [Complex.mul_re, Complex.normSq_apply] using this
  have r11 : Complex.normSq b + Complex.normSq d = 1 := by
    have := congrArg Complex.re e11; simpa [Complex.mul_re, Complex.normSq_apply] using this
  have s00 : Complex.normSq a + Complex.normSq b = 1 := by
    have := congrArg Complex.re f00; simpa [Complex.mul_re, Complex.normSq_apply] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  · exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  · linarith
  · rw [mul_comm c]; simpa using e10

theorem solution
    (t1Prime r1 r1Prime t1 t2 r2Prime r2 t2Prime : ℂ) (theta : ℝ)
    (h1 : beamMatrix t1Prime r1 r1Prime t1 ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (h2 : beamMatrix t2 r2Prime r2 t2Prime ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    let z := Complex.exp (Complex.I * (theta : ℂ))
    let tMPrime := t1Prime * t2 + z * r1Prime * r2Prime
    let rM := r1 * t2 + z * t1 * r2Prime
    let rMPrime := t1Prime * r2 + z * r1Prime * t2Prime
    let tM := r1 * r2 + z * t1 * t2Prime
    let M := mziMatrix (beamMatrix t1Prime r1 r1Prime t1)
      (beamMatrix t2 r2Prime r2 t2Prime) theta
    M = beamMatrix tMPrime rM rMPrime tM ∧
      M ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ‖rMPrime‖ = ‖rM‖ ∧ ‖tM‖ = ‖tMPrime‖ ∧
      ‖rM‖ ^ 2 + ‖tM‖ ^ 2 = 1 ∧
      star rM * tMPrime + rMPrime * star tM = 0 := by
  intro z tMPrime rM rMPrime tM M
  have hM : M = beamMatrix tMPrime rM rMPrime tM := by
    simp only [M, mziMatrix, beamMatrix, phaseMatrix, tMPrime, rM, rMPrime, tM, z]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hP : phaseMatrix theta ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [map_mul, Complex.conj_ofReal]
  have hU : M ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ h2 hP) h1
  refine ⟨hM, hU, ?_⟩
  rw [hM] at hU
  exact x4mzi_entries _ _ _ _ hU

#print axioms solution
