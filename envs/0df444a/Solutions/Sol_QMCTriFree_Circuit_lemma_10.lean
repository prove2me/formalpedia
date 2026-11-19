-- Prove2me | solution 1 for QMCTriFree.Circuit.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:28:08.95519+00:00
-- url     : https://prove2.me/submissions/ad74cf5c-1689-487d-aa0a-0df853d6efac

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory
open QMCTriFree.Circuit

private lemma kronAll_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    QAlgorithms.kronAll A * QAlgorithms.kronAll B = QAlgorithms.kronAll (fun k => A k * B k) := by
  ext x z
  simp only [QAlgorithms.kronAll, Matrix.mul_apply, Matrix.of_apply]
  have h1 : ∀ y : QAlgorithms.Qubits n,
      (∏ k : Fin n, A k (x k) (y k)) * (∏ k : Fin n, B k (y k) (z k)) =
      ∏ k : Fin n, (A k (x k) (y k) * B k (y k) (z k)) := fun y =>
    (Finset.prod_mul_distrib).symm
  simp_rw [h1]
  exact (Fintype.prod_sum (fun k b => A k (x k) b * B k b (z k))).symm

private lemma kronAll_trace {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) :
    (QAlgorithms.kronAll A).trace = ∏ k : Fin n, (A k).trace := by
  simp only [QAlgorithms.kronAll, Matrix.trace, Matrix.diag, Matrix.of_apply]
  exact (Fintype.prod_sum (fun k b => A k b b)).symm

private lemma trace_pauli1_succ (a : Fin 3) : (pauli1 a.succ).trace = 0 := by
  fin_cases a <;>
    simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.trace,
      Matrix.diag, Fintype.sum_bool]

private lemma trace_rho1 (u : Fin 3 → ℝ) : (rho1 u).trace = 1 := by
  unfold rho1 pauliVec
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_bool]
  have h0 : (∑ a : Fin 3, (u a : ℂ) • pauli1 a.succ).trace = 0 := by
    rw [Matrix.trace_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.trace_smul, trace_pauli1_succ a, smul_zero]
  rw [h0, add_zero, smul_eq_mul]
  norm_num

private lemma trace_pauli1_mul_pauli1 (a b : Fin 3) :
    (pauli1 a.succ * pauli1 b.succ).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Fintype.sum_bool] <;> ring

private lemma trace_pauli1_succ_mul_rho1 (a : Fin 3) (u : Fin 3 → ℝ) :
    (pauli1 a.succ * rho1 u).trace = (u a : ℂ) := by
  unfold rho1 pauliVec
  rw [Matrix.mul_smul, Matrix.trace_smul, mul_add, mul_one, Matrix.trace_add,
    trace_pauli1_succ a, zero_add, Finset.mul_sum, Matrix.trace_sum]
  have hterm : ∀ b : Fin 3, (pauli1 a.succ * (u b : ℂ) • pauli1 b.succ).trace =
      if a = b then (2 : ℂ) * (u a : ℂ) else 0 := by
    intro b
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_pauli1_mul_pauli1 a b, smul_eq_mul]
    split_ifs with hab
    · subst hab; ring
    · simp
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, smul_eq_mul]
  ring

private lemma trace_pauliOp_pairStr_mul_rho0 {n : ℕ} (v : Fin n → Fin 3 → ℝ)
    (i j : Fin n) (hij : i ≠ j) (a : Fin 3) :
    (pauliOp (pairStr a.succ i j) * rho0 v).trace = (v i a : ℂ) * (v j a : ℂ) := by
  unfold pauliOp rho0
  rw [kronAll_mul, kronAll_trace]
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin n)) :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase Finset.univ _ hi]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ hj]
  have hrest : ∏ k ∈ (Finset.univ.erase i).erase j,
      (pauli1 (pairStr a.succ i j k) * rho1 (v k)).trace = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    simp only [Finset.mem_erase, ne_eq] at hk
    have hkj : k ≠ j := hk.1
    have hki : k ≠ i := hk.2.1
    simp [pairStr, hki, hkj, pauli1, trace_rho1]
  rw [hrest, mul_one]
  have hpi : pairStr a.succ i j i = a.succ := by simp [pairStr]
  have hpj : pairStr a.succ i j j = a.succ := by simp [pairStr]
  rw [hpi, hpj, trace_pauli1_succ_mul_rho1, trace_pauli1_succ_mul_rho1]

theorem solution {n : ℕ} (v : Fin n → Fin 3 → ℝ) (hv : ∀ k, v k ⬝ᵥ v k = 1)
    (i j : Fin n) (hij : i ≠ j) :
    energy (hEdge i j) (rho0 v) = (1 / 2 : ℝ) * (1 - v i ⬝ᵥ v j) := by
  unfold energy hEdge
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp only [sub_mul, one_mul, Matrix.trace_sub]
  have h1 : (rho0 v).trace = 1 := by
    unfold rho0
    rw [kronAll_trace]
    exact Finset.prod_eq_one fun k _ => trace_rho1 (v k)
  rw [h1]
  rw [show (1 : Fin 4) = Fin.succ 0 from rfl,
      show (2 : Fin 4) = Fin.succ 1 from rfl,
      show (3 : Fin 4) = Fin.succ 2 from rfl]
  rw [trace_pauliOp_pairStr_mul_rho0 v i j hij 0,
      trace_pauliOp_pairStr_mul_rho0 v i j hij 1,
      trace_pauliOp_pairStr_mul_rho0 v i j hij 2]
  have hre : ((1 / 2 : ℂ) • (1 - (v i 0 : ℂ) * (v j 0 : ℂ) -
      (v i 1 : ℂ) * (v j 1 : ℂ) - (v i 2 : ℂ) * (v j 2 : ℂ))).re =
      (1 / 2 : ℝ) * (1 - v i 0 * v j 0 - v i 1 * v j 1 - v i 2 * v j 2) := by
    simp [smul_eq_mul]
  rw [hre]
  simp only [dotProduct, Fin.sum_univ_three]
  ring
