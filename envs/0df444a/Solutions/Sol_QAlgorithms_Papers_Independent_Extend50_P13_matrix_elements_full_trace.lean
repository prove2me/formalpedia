-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P13.matrix_elements_full_trace
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:03:01.780216+00:00
-- url     : https://prove2.me/submissions/9a41f28a-61b4-45d4-9be4-6108f29828c5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

namespace Aux_P13full
open QAlgorithms.Papers.Independent.Extend50.P13

theorem key {I : Type*} [Fintype I] {r : ℕ}
    (P : Matrix (Fin (r + 1) → I) (Fin (r + 1) → I) ℂ) (X : Fin r → Matrix I I ℂ)
    (v w : I → ℂ) :
    finiteMatrixElement w (contractInputs P X) v =
      Matrix.trace (P * tensorMatrices (Fin.lastCases (rankOneOperator v w) X)) := by
  let e : I × (Fin r → I) ≃ (Fin (r + 1) → I) :=
    { toFun := fun p => append p.2 p.1
      invFun := fun u => (u (Fin.last r), fun i => u i.castSucc)
      left_inv := fun p => by simp [append]
      right_inv := fun u => by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [append] }
  have hsum : ∀ F : (Fin (r + 1) → I) → ℂ, ∑ U, F U = ∑ a, ∑ x, F (append x a) := by
    intro F
    rw [← e.sum_comp F, Fintype.sum_prod_type]
    rfl
  have hT : ∀ a x b y, tensorMatrices (Fin.lastCases (rankOneOperator v w) X)
      (append y b) (append x a) = (∏ i, X i (y i) (x i)) * (v b * conj (w a)) := by
    intro a x b y
    unfold tensorMatrices
    rw [Fin.prod_univ_castSucc]
    simp only [append, rankOneOperator, Fin.lastCases_castSucc, Fin.lastCases_last]
  unfold finiteMatrixElement contractInputs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hsum, hT]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (∑ x : Fin r → I, ∑ b : I, ∑ y : Fin r → I,
      P (append x a) (append y b) * ((∏ i, X i (y i) (x i)) * (v b * conj (w a)))) =
      ∑ b : I, ∑ x : Fin r → I, ∑ y : Fin r → I,
      P (append x a) (append y b) * ((∏ i, X i (y i) (x i)) * (v b * conj (w a)))
      from Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

end Aux_P13full

open QAlgorithms.Papers.Independent.Extend50.P13 in
theorem solution {d r : ℕ} (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition (r+1) (r+1))
    (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) (v w : Fin d → ℂ) :
    finiteMatrixElement w (polarizedMap lambda X) v =
      Matrix.trace (centralProjector d lambda * tensorMatrices (Fin.lastCases (rankOneOperator v w) X)) := by
  unfold polarizedMap
  exact Aux_P13full.key _ _ _ _

end
