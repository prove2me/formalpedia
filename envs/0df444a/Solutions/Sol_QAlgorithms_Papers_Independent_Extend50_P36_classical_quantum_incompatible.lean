-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P36.classical_quantum_incompatible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:15:53.459375+00:00
-- url     : https://prove2.me/submissions/0918706e-e416-482a-9806-8db89155ffeb

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36
noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

end QAlgorithms.Papers.Independent.Extend50.P36

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P36
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped ComplexOrder

theorem cq_psd_offdiag_zero {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) {i j : n} (hii : M i i = 0) : M i j = 0 := by
  by_cases hij : i = j
  · subst hij; exact hii
  set N := M.submatrix ![i, j] ![i, j] with hN
  have hNp : N.PosSemidef := hM.submatrix _
  have h00 : N 0 0 = 0 := by simp [hN, hii]
  have h10 : N 1 0 = star (N 0 1) := by
    have := hNp.1.apply 1 0; rw [← this]
  set z := N 0 1 with hz
  by_contra hz0
  have hw : 0 < Complex.normSq z := Complex.normSq_pos.2 (fun h => hz0 (by simpa [hz, hN] using h))
  set t : ℝ := ((N 1 1).re + 1) / (2 * Complex.normSq z)
  have h := hNp.dotProduct_mulVec_nonneg ![-(t : ℂ) * z, 1]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.star_apply, h00, h10] at h
  have hre := (Complex.le_def.1 h).1
  simp [Complex.mul_re, Complex.mul_im] at hre
  have key : t * (2 * Complex.normSq z) = (N 1 1).re + 1 := by
    simp only [t]; field_simp
  rw [Complex.normSq_apply] at key
  nlinarith [key]

theorem cq_true_apply (a b c d : Fin 2) : cqWitness true (a, b) (c, d) =
    if (a = c ∧ b = d) ∨ (a ≠ c ∧ b ≠ d) then 1/4 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cqWitness, Matrix.kronecker_apply, Matrix.one_apply] <;> norm_num

theorem cq_false_apply (a b c d : Fin 2) : cqWitness false (a, b) (c, d) =
    if a = c ∧ b = d ∧ a = b then 1/2 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cqWitness, Matrix.kronecker_apply, Matrix.one_apply] <;> norm_num


theorem cq_true_density : IsDensityMatrix (cqWitness true) := by
  have he : cqWitness true =
      Matrix.vecMulVec (fun p : Fin 2 × Fin 2 => if p.1 = p.2 then (1/2 : ℂ) else 0)
        (star fun p : Fin 2 × Fin 2 => if p.1 = p.2 then (1/2 : ℂ) else 0) +
      Matrix.vecMulVec (fun p : Fin 2 × Fin 2 => if p.1 ≠ p.2 then (1/2 : ℂ) else 0)
        (star fun p : Fin 2 × Fin 2 => if p.1 ≠ p.2 then (1/2 : ℂ) else 0) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    rw [cq_true_apply]
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [Matrix.vecMulVec_apply] <;> norm_num
  refine ⟨?_, ?_⟩
  · rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star _).add (Matrix.posSemidef_vecMulVec_self_star _)
  · simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, cq_true_apply]
    norm_num

theorem cq_false_density : IsDensityMatrix (cqWitness false) := by
  have he : cqWitness false =
      Matrix.diagonal (fun p : Fin 2 × Fin 2 => if p.1 = p.2 then (1/2 : ℂ) else 0) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    rw [cq_false_apply]
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [Matrix.diagonal_apply]
  refine ⟨?_, ?_⟩
  · rw [he]
    refine Matrix.PosSemidef.diagonal ?_
    intro p
    by_cases h : p.1 = p.2 <;> simp [h]
  · simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, cq_false_apply]
    norm_num

theorem cq_traceRight (b : Bool) : traceRight (cqWitness b) = fullyMixed (Fin 2) := by
  ext i j
  cases b <;>
  · simp only [traceRight, Matrix.of_apply, Fin.sum_univ_two, cq_true_apply, cq_false_apply,
      fullyMixed, Matrix.smul_apply, Matrix.one_apply, Fintype.card_fin]
    fin_cases i <;> fin_cases j <;> simp <;> norm_num

theorem cq_not_joinable : ¬ JoinableTwo (cqWitness true) (cqWitness false) := by
  rintro ⟨X, ⟨hpsd, -⟩, hAB, hAC⟩
  have hdiag : ∀ a c : Fin 2, a ≠ c → ∀ b, X (a, b, c) (a, b, c) = 0 := by
    intro a c hac b
    have h := congrFun (congrFun hAC (a, c)) (a, c)
    simp only [idTensorSuperop, traceLeft, Matrix.of_apply, Fin.sum_univ_two, cq_false_apply] at h
    rw [if_neg (by tauto)] at h
    have h0 := hpsd.diag_nonneg (i := (a, 0, c))
    have h1 := hpsd.diag_nonneg (i := (a, 1, c))
    have := (add_eq_zero_iff_of_nonneg h0 h1).1 h
    fin_cases b
    · exact this.1
    · exact this.2
  have h := congrFun (congrFun hAB ((0 : Fin 2), (0 : Fin 2))) ((1 : Fin 2), (1 : Fin 2))
  simp only [idTensorSuperop, traceRight, Matrix.of_apply, Fin.sum_univ_two, cq_true_apply] at h
  have e1 : X (0, 0, 1) (1, 1, 1) = 0 := cq_psd_offdiag_zero hpsd (hdiag 0 1 (by decide) 0)
  have e0 : X (0, 0, 0) (1, 1, 0) = 0 := by
    have h2 : X (1, 1, 0) (0, 0, 0) = 0 := cq_psd_offdiag_zero hpsd (hdiag 1 0 (by decide) 1)
    have := hpsd.1.apply (0, 0, 0) (1, 1, 0)
    rw [← this, h2, star_zero]
  rw [e0, e1] at h
  norm_num at h


theorem cq_false_cq : IsClassicalQuantum (cqWitness false) := by
  refine ⟨1, fun _ => 1/2, fun i => Matrix.diagonal (fun j => if j = i then 1 else 0),
    fun _ => by norm_num, by simp <;> norm_num, fun i => ⟨?_, ?_⟩, ?_⟩
  · exact Matrix.PosSemidef.diagonal (fun j => by by_cases h : j = i <;> simp [h])
  · simp [Matrix.trace]
  · ext ⟨a, b⟩ ⟨c, d⟩
    rw [cq_false_apply]
    simp only [Matrix.sum_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.kronecker_apply,
      Submonoid.coe_one, one_mul, Matrix.conjTranspose_one, mul_one, Matrix.add_apply]
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [Matrix.diagonal_apply] <;> norm_num

noncomputable def cqHad : Matrix (Fin 2) (Fin 2) ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • !![1, 1; 1, -1]

theorem cqHad_sq : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem cqHad_mem : cqHad ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cqHad, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, cqHad_sq] <;> norm_num

theorem cqHad_proj (i : Fin 2) :
    cqHad * Matrix.diagonal (fun j => if j = i then 1 else 0) * cqHadᴴ =
      !![1/2, (if i = 0 then 1/2 else -1/2); (if i = 0 then 1/2 else -1/2), 1/2] := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [cqHad, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.diagonal_apply] <;>
    first | rfl | linear_combination cqHad_sq | linear_combination -cqHad_sq | ring

theorem cq_true_cq : IsClassicalQuantum (cqWitness true) := by
  refine ⟨⟨cqHad, cqHad_mem⟩, fun _ => 1/2,
    fun i => cqHad * Matrix.diagonal (fun j => if j = i then 1 else 0) * cqHadᴴ,
    fun _ => by norm_num, by simp <;> norm_num, fun i => ⟨?_, ?_⟩, ?_⟩
  · exact (Matrix.PosSemidef.diagonal (fun j => by by_cases h : j = i <;> simp [h])).mul_mul_conjTranspose_same _
  · beta_reduce; rw [cqHad_proj]; simp [Matrix.trace]; norm_num
  · simp only [cqHad_proj]
    ext ⟨a, b⟩ ⟨c, d⟩
    rw [cq_true_apply]
    simp only [Matrix.sum_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.kronecker_apply]
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp <;> norm_num

theorem solution :
    IsDensityMatrix (cqWitness true) ∧ IsDensityMatrix (cqWitness false) ∧
    IsClassicalQuantum (cqWitness true) ∧ IsClassicalQuantum (cqWitness false) ∧
    traceRight (cqWitness true) = fullyMixed (Fin 2) ∧
    traceRight (cqWitness false) = fullyMixed (Fin 2) ∧
    ¬ JoinableTwo (cqWitness true) (cqWitness false) :=
  ⟨cq_true_density, cq_false_density, cq_true_cq, cq_false_cq, cq_traceRight true,
    cq_traceRight false, cq_not_joinable⟩
