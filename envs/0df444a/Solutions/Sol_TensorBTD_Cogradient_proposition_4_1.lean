-- Prove2me | solution 1 for TensorBTD.Cogradient.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:30:04.414539+00:00
-- url     : https://prove2.me/submissions/d95d80af-315a-4dc2-bc6b-019c11f4d1b2

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_TensorBTD_Cogradient_Setting

set_option backward.isDefEq.respectTransparency false
open TensorBTD.Gramian TensorBTD.Cogradient Matrix
private lemma fullVec_affine {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (z d : Unk I L → ℂ) (t : ℂ) : fullVec (z + t • d) = fullVec z + t • fullVec d := by
  classical
  funext g
  rcases g with ⟨n,c,i⟩
  cases n with
  | inl p => rfl
  | inr q =>
    simp only [fullVec, factor, cMat, Matrix.mul_apply, Matrix.of_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    congr 1
    simp_rw [mul_assoc]
    rw [Finset.mul_sum]

private lemma fullVec_single {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (b : Unk I L) (g : GIdx I L) :
    fullVec (Pi.single b 1) g = Sigma I L b g := by
  classical
  rcases b with ⟨n,b⟩
  rcases g with ⟨m,g⟩
  by_cases h : n = m
  · subst m
    rw [TensorBTD.Gramian.Sigma, Matrix.blockDiagonal'_apply_eq]
    cases n <;> dsimp only [UCol] at * <;> rcases b with ⟨c,i⟩ <;> rcases g with ⟨r,j⟩ <;>
      simp [fullVec, factor, aMat, cMat, E, SigmaBlock, F,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.mul_apply,
        Pi.single_apply, ite_and, eq_comm]
    all_goals split_ifs <;> rfl
  · rw [TensorBTD.Gramian.Sigma, Matrix.blockDiagonal'_apply_ne _ _ _ h]
    cases n <;> cases m <;>
      simp_all [fullVec, factor, aMat, cMat, Matrix.mul_apply, Pi.single_apply]

private lemma deriv_line {X : Type*} [Fintype X] [DecidableEq X]
    (g : (X → ℂ) → ℂ) (x d : X → ℂ) (hg : DifferentiableAt ℝ g x) :
    deriv (fun t : ℝ => g (x + (t : ℂ) • d)) 0 = fderiv ℝ g x d := by
  have hp : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const d)
  have h := hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)
  convert h.deriv using 1
  congr 1

private lemma fullVec_basis {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (q : Fin Q) (i : Fin (I (.inr q))) (r : Fin R) :
    fullVec (Pi.single (⟨.inr q,(r,i)⟩ : Unk I L) 1) =
      ∑ c : Col L, if c.1 = r then Pi.single (⟨.inr q,(c,i)⟩ : GIdx I L) 1 else 0 := by
  classical
  funext b
  rcases b with ⟨m,c,j⟩
  cases m with
  | inl p => simp [fullVec, factor, aMat, ite_apply, Pi.single_apply]
  | inr q' =>
    by_cases hq : q' = q
    · subst q'
      simp [fullVec, factor, cMat, E, Matrix.mul_apply, ite_apply, Pi.single_apply, ite_and, eq_comm]
      rw [Finset.sum_eq_single c]
      · simp
      · intro b hb hbc
        simp [Ne.symm hbc]
      · simp
    · simp [fullVec, factor, cMat, E, Matrix.mul_apply, ite_apply, Pi.single_apply, hq, Ne.symm hq]

private lemma cograd_of_differentiable {X : Type*} [Fintype X] [DecidableEq X]
    (g : (X → ℂ) → ℂ) (x : X → ℂ) (hg : DifferentiableAt ℝ g x) (b : X) :
    cograd g x b = (1/2 : ℂ) * (fderiv ℝ g x (Pi.single b 1) -
      Complex.I * fderiv ℝ g x (Complex.I • Pi.single b 1)) := by
  unfold cograd
  rw [deriv_line g x _ hg]
  have h : (fun t : ℝ => g (x + ((t : ℂ) * Complex.I) • Pi.single b 1)) =
      (fun t : ℝ => g (x + (t : ℂ) • (Complex.I • Pi.single b 1))) := by
    funext t; rw [mul_smul]
  rw [h, deriv_line g x _ hg]
theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} :
    (∀ (q : Fin Q) (C : Matrix (Fin (I (.inr q))) (Fin R) ℂ),
      vec (C * TensorBTD.Gramian.E L) = vecMul (vec C) (kronecker (TensorBTD.Gramian.E L) (1 : Matrix (Fin (I (.inr q))) (Fin (I (.inr q))) ℂ))) ∧
    ∀ (g : (TensorBTD.Gramian.GIdx I L → ℂ) → ℂ) (z : TensorBTD.Gramian.Unk I L → ℂ), DifferentiableAt ℝ g (TensorBTD.Gramian.fullVec z) →
      ∀ q : Fin Q, cogradC (g ∘ TensorBTD.Gramian.fullVec) z q = cogradMatG g (TensorBTD.Gramian.fullVec z) (.inr q) * (TensorBTD.Gramian.E L)ᵀ := by
  classical
  constructor
  · intro q C
    exact Matrix.vec_mul_eq_vecMul C (E L)
  · intro g z hg q
    ext i r
    change cograd (g ∘ fullVec) z ⟨.inr q,(r,i)⟩ = _
    unfold cograd
    simp only [Function.comp_def, fullVec_affine]
    have hi : (fun t : ℝ => g (fullVec z + ((t : ℂ) * Complex.I) •
        fullVec (Pi.single (⟨.inr q,(r,i)⟩ : Unk I L) 1))) =
        (fun t : ℝ => g (fullVec z + (t : ℂ) • (Complex.I •
        fullVec (Pi.single (⟨.inr q,(r,i)⟩ : Unk I L) 1)))) := by
      funext t; rw [mul_smul]
    rw [hi, deriv_line g (fullVec z) _ hg, deriv_line g (fullVec z) _ hg]
    rw [fullVec_basis]
    simp only [Finset.smul_sum, map_sum]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cogradMatG, Matrix.of_apply, E]
    simp_rw [cograd_of_differentiable g (fullVec z) hg]
    simp only [mul_ite, mul_one, mul_zero, smul_ite, smul_zero, apply_ite, map_zero]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp

#print axioms solution



