-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.cq_hadamard_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:46:53.460746+00:00
-- url     : https://prove2.me/submissions/6cf44f1d-c3e1-4e59-bdeb-a80a497b6341

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_gram (x : A → EuclideanSpace ℂ B) (k k' : A) :
    QAlgorithms.Papers.Independent.Claimed50.P48.gram x k k' = ∑ b, star (x k' b) * x k b := by
  simp [QAlgorithms.Papers.Independent.Claimed50.P48.gram, PiLp.inner_apply, mul_comm]

theorem x8_entry (U : Matrix.unitaryGroup A ℂ) (x : A → EuclideanSpace ℂ B) (rho : Matrix A A ℂ)
    (k k' : A) :
    complementaryChannel (indexedKrausDilation (rankOneKraus (basisColumns U) x)) rho k k' =
      gram x k k' * ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ)) k k' := by
  rw [x8_gram]
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, mul_apply, conjTranspose_apply,
    indexedKrausDilation, rankOneKraus, basisColumns, Finset.sum_mul, Finset.mul_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [RCLike.star_def]
  ring

theorem x8_main [Nonempty A] [Nonempty B]
    (U : Matrix.unitaryGroup A ℂ) (x : A → EuclideanSpace ℂ B)
    (hx : ∀ k, IsState (x k)) :
    let F := rankOneKraus (basisColumns U) x
    complementaryChannel (indexedKrausDilation F) =
      (fun rho => Matrix.hadamard (gram x) ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) ∧
    ∃ r : ℕ, ∃ R : Fin r → Matrix A A ℂ,
      (∀ m i j, i ≠ j → R m i j = 0) ∧
      complementaryChannel (indexedKrausDilation F) =
        (fun rho => krausApply R ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) := by
  intro F
  have h1 : complementaryChannel (indexedKrausDilation F) =
      (fun rho => Matrix.hadamard (gram x) ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) := by
    funext rho; ext k k'
    rw [x8_entry]; rfl
  refine ⟨h1, Fintype.card B, fun m => diagonal fun k => x k ((Fintype.equivFin B).symm m), ?_, ?_⟩
  · intro m i j hij; exact diagonal_apply_ne _ hij
  · rw [h1]; funext rho
    generalize (U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ) = Y
    ext k k'
    simp only [krausApply, Matrix.sum_apply, diagonal_mul, mul_diagonal, conjTranspose_apply,
      hadamard_apply, diagonal_conjTranspose]
    rw [x8_gram, Finset.sum_mul]
    rw [← Equiv.sum_comp (Fintype.equivFin B).symm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [RCLike.star_def]
    ring

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48
  QAlgorithms.Papers.Independent.Information100.P67 in
theorem solution {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (U : Matrix.unitaryGroup A ℂ) (x : A → EuclideanSpace ℂ B)
    (hx : ∀ k, IsState (x k)) :
    let F := rankOneKraus (basisColumns U) x
    complementaryChannel (indexedKrausDilation F) =
      (fun rho => Matrix.hadamard (gram x) ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) ∧
    ∃ r : ℕ, ∃ R : Fin r → Matrix A A ℂ,
      (∀ m i j, i ≠ j → R m i j = 0) ∧
      complementaryChannel (indexedKrausDilation F) =
        (fun rho => krausApply R ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) :=
  x8_main U x hx
