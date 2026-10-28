-- Prove2me | solution 1 for QAlgorithms.Nannicini.norm_prod_sub_prod_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:00:42.462408+00:00
-- url     : https://prove2.me/submissions/e15c7c17-4b41-4eb7-ae13-b3a95efd9f5d

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini.A3NP
open QAlgorithms Matrix
open scoped Matrix.Norms.L2Operator

lemma specNorm_eq {q : ℕ} (A : Matrix (Qubits q) (Qubits q) ℂ) : specNorm A = ‖A‖ := rfl

lemma norm_unitary_le {q : ℕ} (U : Matrix (Qubits q) (Qubits q) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits q) ℂ) : ‖U‖ ≤ 1 := by
  have h1 : ‖Uᴴ * U‖ = ‖U‖ * ‖U‖ := Matrix.l2_opNorm_conjTranspose_mul_self U
  have h2 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [h2] at h1
  have h3 : ‖(1 : Matrix (Qubits q) (Qubits q) ℂ)‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x; simp
  nlinarith [norm_nonneg U]

lemma prod_mem {q T : ℕ} (U : Fin T → Matrix (Qubits q) (Qubits q) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Qubits q) ℂ) :
    (List.ofFn U).prod ∈ Matrix.unitaryGroup (Qubits q) ℂ := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.ofFn_succ, List.prod_cons]
    exact Submonoid.mul_mem _ (hU 0) (ih _ fun j => hU _)

theorem main (q T : ℕ) (U V : Fin T → Matrix (Qubits q) (Qubits q) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Qubits q) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Qubits q) ℂ) :
    specNorm ((List.ofFn U).prod - (List.ofFn V).prod) ≤ ∑ j, specNorm (U j - V j) := by
  simp only [specNorm_eq]
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Fin.sum_univ_succ]
    set P := (List.ofFn fun i : Fin T => U i.succ).prod
    set Q := (List.ofFn fun i : Fin T => V i.succ).prod
    have hQ : ‖Q‖ ≤ 1 := norm_unitary_le _ (prod_mem _ fun j => hV _)
    have hU0 : ‖U 0‖ ≤ 1 := norm_unitary_le _ (hU 0)
    have e : U 0 * P - V 0 * Q = U 0 * (P - Q) + (U 0 - V 0) * Q := by noncomm_ring
    have ih' := ih (fun i => U i.succ) (fun i => V i.succ) (fun j => hU _) (fun j => hV _)
    rw [e]
    calc ‖U 0 * (P - Q) + (U 0 - V 0) * Q‖
        ≤ ‖U 0 * (P - Q)‖ + ‖(U 0 - V 0) * Q‖ := norm_add_le _ _
      _ ≤ ‖U 0‖ * ‖P - Q‖ + ‖U 0 - V 0‖ * ‖Q‖ :=
          add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
      _ ≤ 1 * ‖P - Q‖ + ‖U 0 - V 0‖ * 1 := by
          gcongr
      _ ≤ _ := by linarith

end QAlgorithms.Nannicini.A3NP

theorem solution (q T : ℕ) (U V : Fin T → Matrix (QAlgorithms.Qubits q) (QAlgorithms.Qubits q) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (QAlgorithms.Qubits q) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (QAlgorithms.Qubits q) ℂ) :
    QAlgorithms.specNorm ((List.ofFn U).prod - (List.ofFn V).prod) ≤
      ∑ j, QAlgorithms.specNorm (U j - V j) :=
  QAlgorithms.Nannicini.A3NP.main q T U V hU hV
