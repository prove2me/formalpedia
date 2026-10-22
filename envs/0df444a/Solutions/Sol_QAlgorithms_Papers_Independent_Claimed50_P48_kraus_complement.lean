-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.kraus_complement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:15:17.008577+00:00
-- url     : https://prove2.me/submissions/a3f7c72c-53dd-4d3f-9bec-a7177a375549

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

theorem g68l_kc1 (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E := by
  funext rho; ext b b'
  simp only [receiverChannel, traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68l_kc2 (E : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (a b : K) :
    complementaryChannel (indexedKrausDilation E) rho a b = (E a * rho * (E b)ᴴ).trace := by
  simp only [complementaryChannel, traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68l_kc3 (E : K → Matrix B A ℂ) :
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) := by
  funext rho; ext a b
  rw [g68l_kc2]
  simp only [krausApply, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]

/-- Equations (10)–(12), PDF p.4: correct alpha,beta trace order and the
computed output-row Kraus family. Twice reshuffling returns the original map. -/
theorem solution [Nonempty A] (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E ∧
    (∀ rho a b, complementaryChannel (indexedKrausDilation E) rho a b = (E a * rho * (E b)ᴴ).trace ∧
      complementaryChannel (indexedKrausDilation E) rho a b = (rho * (E b)ᴴ * E a).trace) ∧
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) ∧
    rowKraus (rowKraus E) = E ∧
    complementaryChannel (indexedKrausDilation (rowKraus E)) = krausApply E := by
  refine ⟨g68l_kc1 E, fun rho a b => ⟨g68l_kc2 E rho a b, ?_⟩, g68l_kc3 E, rfl, ?_⟩
  · rw [g68l_kc2, Matrix.mul_assoc, Matrix.trace_mul_comm]
  · rw [g68l_kc3]; rfl



end
