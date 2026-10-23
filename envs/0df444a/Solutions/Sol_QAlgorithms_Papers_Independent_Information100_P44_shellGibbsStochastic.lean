-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.shellGibbsStochastic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:51:16.679124+00:00
-- url     : https://prove2.me/submissions/931905e9-b1e5-4455-b90b-33c2be353569

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma X7_shell_apply {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (r i : Fin d) (a : Fin b × Fin b) :
    (shellVector D r i) a = thermalKraus D a r i := by
  simp only [shellVector]
  split_ifs with h
  · rfl
  · simp only [thermalKraus]
    rw [D.support r i a.2 a.1 (fun h' => h h'), mul_zero]

lemma X7_gibbs_nonneg {n : ℕ} (E : Fin n → ℝ) (beta : ℝ) (i : Fin n) : 0 ≤ gibbsWeight E beta i := by
  unfold gibbsWeight
  exact div_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)

lemma X7_gibbs_sum {n : ℕ} (hn : 0 < n) (E : Fin n → ℝ) (beta : ℝ) :
    ∑ i, gibbsWeight E beta i = 1 := by
  unfold gibbsWeight
  rw [← Finset.sum_div]
  apply div_self
  apply ne_of_gt
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma X7_shell_normsq {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (r i : Fin d) :
    ‖shellVector D r i‖ ^ 2 = ∑ a : Fin b × Fin b, gibbsWeight D.bathEnergy beta a.1 *
      ‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [X7_shell_apply]
  simp only [thermalKraus, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (X7_gibbs_nonneg _ _ _)]

lemma X7_col {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix.unitaryGroup n ℂ) (c : n) :
    ∑ k, ‖(U : Matrix n n ℂ) k c‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp U.2) c) c
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have : ((∑ k, ‖(U : Matrix n n ℂ) k c‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]; push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.mul_conj', mul_comm]; rfl
  exact_mod_cast this

lemma X7_row {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix.unitaryGroup n ℂ) (c : n) :
    ∑ k, ‖(U : Matrix n n ℂ) c k‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp U.2) c) c
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have : ((∑ k, ‖(U : Matrix n n ℂ) c k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]; push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.mul_conj']; rfl
  exact_mod_cast this

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) :
    (∀ i, (∑ r, ‖shellVector D r i‖ ^ 2) = 1) ∧
    (∀ r, (∑ i, ‖shellVector D r i‖ ^ 2 * gibbsWeight E beta i) = gibbsWeight E beta r) := by
  constructor
  · intro i
    simp_rw [X7_shell_normsq]
    calc ∑ r, ∑ a : Fin b × Fin b, gibbsWeight D.bathEnergy beta a.1 * ‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)‖ ^ 2
        = ∑ μ, gibbsWeight D.bathEnergy beta μ * ∑ k : Fin d × Fin b, ‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) k (i, μ)‖ ^ 2 := by
          simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
          rw [Finset.sum_comm]
      _ = 1 := by
          simp_rw [X7_col, mul_one]
          exact X7_gibbs_sum D.bathPositive _ _
  · intro r
    simp_rw [X7_shell_normsq, Finset.sum_mul]
    have key : ∀ (i : Fin d) (a : Fin b × Fin b),
        gibbsWeight D.bathEnergy beta a.1 * ‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)‖ ^ 2 * gibbsWeight E beta i =
        gibbsWeight E beta r * (gibbsWeight D.bathEnergy beta a.2 * ‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)‖ ^ 2) := by
      intro i a
      by_cases h : E i + D.bathEnergy a.1 = E r + D.bathEnergy a.2
      · unfold gibbsWeight
        have : Real.exp (-beta * D.bathEnergy a.1) * Real.exp (-beta * E i) =
            Real.exp (-beta * E r) * Real.exp (-beta * D.bathEnergy a.2) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; linear_combination (-beta) * h
        simp only [div_eq_mul_inv]
        linear_combination (‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)‖ ^ 2 * (∑ j, Real.exp (-beta * D.bathEnergy j))⁻¹ *
          (∑ j, Real.exp (-beta * E j))⁻¹) * this
      · simp [D.support r i a.2 a.1 h]
    simp_rw [key, ← Finset.mul_sum]
    conv_rhs => rw [← mul_one (gibbsWeight E beta r)]
    congr 1
    calc ∑ i, ∑ a : Fin b × Fin b, gibbsWeight D.bathEnergy beta a.2 * ‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)‖ ^ 2
        = ∑ ν, gibbsWeight D.bathEnergy beta ν * ∑ k : Fin d × Fin b, ‖(D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, ν) k‖ ^ 2 := by
          simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
          conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
      _ = 1 := by
          simp_rw [X7_row, mul_one]
          exact X7_gibbs_sum D.bathPositive _ _


end
