-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.proposition2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:09:01.597211+00:00
-- url     : https://prove2.me/submissions/1c0778d5-bfdf-4ac7-be4b-48cc79b949db

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

theorem s110p_slot_trace {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ} (j : Fin k)
    (rho A : Mat I) (B : Mat ({c : Fin k // c ≠ j} → I)) :
    (tensorPower k rho * slotFactor j A B).trace = (rho * A).trace *
      ∑ x : {c : Fin k // c ≠ j} → I, ∑ y : {c : Fin k // c ≠ j} → I,
        (∏ c, rho (x c) (y c)) * B y x := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tensorPower, slotFactor]
  have hinner : ∀ x : Fin k → I, ∑ y : Fin k → I, (∏ c, rho (x c) (y c)) *
      (A (y j) (x j) * B (fun c => y c.1) (fun c => x c.1)) =
      ∑ q : I × ({c : Fin k // c ≠ j} → I), rho (x j) q.1 * A q.1 (x j) *
        ((∏ c : {c : Fin k // c ≠ j}, rho (x c) (q.2 c)) * B q.2 (fun c => x c.1)) := by
    intro x
    rw [← (Equiv.funSplitAt j I).symm.sum_comp]
    refine Fintype.sum_congr _ _ (fun q => ?_)
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    obtain ⟨b, y'⟩ := q
    have h1 : (Equiv.funSplitAt j I).symm (b, y') j = b := by simp
    have h2 : ∀ c : {c : Fin k // c ≠ j}, (Equiv.funSplitAt j I).symm (b, y') c.1 = y' c := by
      intro c; simp [c.2]
    simp only [h1, h2]
    ring
  simp only [hinner]
  rw [← (Equiv.funSplitAt j I).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ a (x' : {c : Fin k // c ≠ j} → I), (Equiv.funSplitAt j I).symm (a, x') j = a := by simp
  have h2 : ∀ a (x' : {c : Fin k // c ≠ j} → I) (c : {c : Fin k // c ≠ j}),
      (Equiv.funSplitAt j I).symm (a, x') c.1 = x' c := by
    intro a x' c; simp [c.2]
  simp only [h1, h2]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul_sum]
theorem s110k_response_eq {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : ExpectationModel I k) (rho : Mat I) :
    M.response rho = (tensorPower k rho * M.effective).trace.re := by
  unfold ExpectationModel.response ExpectationModel.effective
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]


theorem s110p_trace_zero {n : ℕ} (L : MatrixLieData (Qubits n)) (rho Aj : Mat (Qubits n))
    (hr : rho ∈ timesI (L.algebra : Set (Mat (Qubits n))))
    (hA : Aj ∈ timesI (lieComplement L)) : (rho * Aj).trace = 0 := by
  obtain ⟨X, hX, rfl⟩ := hr
  obtain ⟨Y, ⟨hYs, hYo⟩, rfl⟩ := hA
  have h := hYo X hX
  rw [hYs] at h
  have h2 : (X * Y).trace = 0 := by
    rw [Matrix.trace_mul_comm]
    have : (-Y * X).trace = -(Y * X).trace := by rw [Matrix.neg_mul, Matrix.trace_neg]
    rw [this] at h
    exact neg_eq_zero.mp h
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, h2]
  simp

theorem s110p_resp_zero {n k : ℕ} (M : ExpectationModel (Qubits n) k)
    (L : MatrixLieData (Qubits n))
    (A : Fin k → Mat (Qubits n))
    (B : (j : Fin k) → Mat ({c : Fin k // c ≠ j} → Qubits n))
    (hA : ∀ j, A j ∈ timesI (lieComplement L))
    (hobs : M.effective ∈ separatedSpan A B) (rho : Mat (Qubits n))
    (hr : rho ∈ timesI (L.algebra : Set (Mat (Qubits n)))) : M.response rho = 0 := by
  rw [s110k_response_eq]
  suffices h : (tensorPower k rho * M.effective).trace = 0 by rw [h]; simp
  unfold separatedSpan at hobs
  generalize M.effective = E at hobs ⊢
  induction hobs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [s110p_slot_trace, s110p_trace_zero L rho (A j) hr (hA j), zero_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.trace_add, hx, hy, add_zero]
  | smul a x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)
open QAlgorithms.Papers.Independent.Information100.P32 (purity)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

theorem solution {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    (L : MatrixLieData (Qubits n))
    (hidentity : Complex.I • (1 : Mat (Qubits n)) ∈ L.algebra)
    (R : Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : DatasetSymmetry (groupMatrices L.group) R label)
    (hinput : R ⊆ timesI (L.algebra : Set (Mat (Qubits n))))
    (A : Fin k → Mat (Qubits n))
    (B : (j : Fin k) → Mat ({c : Fin k // c ≠ j} → Qubits n))
    (hA : ∀ j, A j ∈ timesI (lieComplement L) ∧ (A j).IsHermitian)
    (hobs : M.effective ∈ separatedSpan A B) :
    DomainInvariant (groupMatrices L.group) R M.response ∧
      ∀ rho ∈ R, M.response rho = 0 := by
  have hz : ∀ rho ∈ R, M.response rho = 0 := fun rho hr =>
    s110p_resp_zero M L A B (fun j => (hA j).1) hobs rho (hinput hr)
  refine ⟨?_, hz⟩
  intro V hV rho hr
  rw [hz rho hr, hz _ ((hdata.2 V hV rho hr).1)]
