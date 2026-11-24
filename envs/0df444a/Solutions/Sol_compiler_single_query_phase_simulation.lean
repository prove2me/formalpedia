-- Prove2me | solution 1 for compiler_single_query_phase_simulation
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-23T22:07:12.679888+00:00
-- url     : https://prove2.me/submissions/7e929e6c-4dcb-421d-9b60-d75f0f3b5f84

import Definitions.Def_QuantumLTF_Majority_PhaseQueryModel




set_option autoImplicit false

open QAlgorithms QuantumLTF.Majority

/- Append the |-> answer qubit used to turn the Boolean oracle into a phase oracle. -/


/- A single Majority bit-oracle call acts by phase kickback on the data register. -/
theorem compiler_majority_phase_kickback {n : ℕ} (A : Finset (Fin n))
    (x : EuclideanSpace ℂ (Qubits n)) (y : Qubits (n+1)) :
    act (majorityOracle A) (compiler_phase_lift x) y =
      (if majorityBit A (fun i => y i.castSucc) then (-1 : ℂ) else 1) *
        compiler_phase_lift x y := by
  classical
  let b := majorityBit A (fun i => y i.castSucc)
  let z : Qubits (n+1) := Fin.snoc (fun i => y i.castSucc) (xor (y (Fin.last n)) b)
  have hhead (i : Fin n) : z i.castSucc = y i.castSucc := by simp [z]
  have hlast : z (Fin.last n) = xor (y (Fin.last n)) b := by simp [z]
  have hb : majorityBit A (fun i => z i.castSucc) = b := by simp [hhead, b]
  have hxor : y (Fin.last n) = xor (z (Fin.last n))
      (majorityBit A (fun i => z i.castSucc)) := by
    rw [hlast, hb]
    cases y (Fin.last n) <;> cases b <;> rfl
  have hunique (w : Qubits (n+1))
      (hh : (∀ i : Fin n, y i.castSucc = w i.castSucc) ∧
        y (Fin.last n) = xor (w (Fin.last n)) (majorityBit A (fun i => w i.castSucc))) :
      w = z := by
    have hwhead : (fun i : Fin n => w i.castSucc) = (fun i => y i.castSucc) :=
      funext (fun i => (hh.1 i).symm)
    have hwbit : majorityBit A (fun i => w i.castSucc) = b := by rw [hwhead]
    have hwlast : w (Fin.last n) = xor (y (Fin.last n)) b := by
      have hh' := hh.2
      rw [hwbit] at hh'
      cases hw : w (Fin.last n) <;> cases hy : y (Fin.last n) <;>
        cases hb' : b <;> simp [hw, hy, hb'] at hh' ⊢
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hwlast, hlast]
    · exact (hh.1 j).symm.trans (hhead j).symm
  change (∑ w : Qubits (n+1), majorityOracle A y w * compiler_phase_lift x w) = _
  rw [Finset.sum_eq_single z]
  · rw [majorityOracle, Matrix.of_apply, if_pos ⟨fun i => (hhead i).symm, hxor⟩, one_mul]
    change (if z (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
        x (fun i => z i.castSucc) =
      (if b then (-1 : ℂ) else 1) *
        ((if y (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
          x (fun i => y i.castSucc))
    simp only [hhead, hlast]
    cases y (Fin.last n) <;> cases b <;> simp
  · intro w _ hw
    have hnot : ¬ ((∀ i : Fin n, y i.castSucc = w i.castSucc) ∧
        y (Fin.last n) = xor (w (Fin.last n)) (majorityBit A (fun i => w i.castSucc))) :=
      fun hh => hw (hunique w hh)
    simp only [majorityOracle, Matrix.of_apply, if_neg hnot, zero_mul]
  · simp

theorem compiler_phase_lift_norm {n : ℕ} (x : EuclideanSpace ℂ (Qubits n)) :
    ‖compiler_phase_lift x‖ = ‖x‖ := by
  have hcoeff : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = (1/2 : ℝ) := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsq : ‖compiler_phase_lift x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+1) => Bool))]
    rw [Fintype.sum_prod_type]
    simp [Fin.snocEquiv, Fintype.sum_bool, compiler_phase_lift,
      norm_mul, mul_pow, hcoeff]
    simp only [← Finset.mul_sum]
    ring
  nlinarith [norm_nonneg (compiler_phase_lift x), norm_nonneg x]

/- The physical one-query block used for phase kickback. -/


theorem compiler_single_majority_query_count (n : ℕ) :
    (compiler_single_majority_query n).queryCount 0 = 1 := by
  simp [compiler_single_majority_query, OracleCircuit.queryCount, OracleStep.IsQueryTo]

theorem compiler_single_majority_query_unitary {n : ℕ} (A : Finset (Fin n)) :
    (compiler_single_majority_query n).unitary (fun _ => majorityOracle A) =
      majorityOracle A := by
  simp only [compiler_single_majority_query, OracleCircuit.unitary, List.map_cons,
    List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.prod_cons, List.prod_nil, mul_one, OracleStep.mat, Bool.false_eq_true, ite_false]
  ext y z
  simp [embedOp]
  rfl

/- Exact one-query phase simulation with a norm-preserving answer-qubit embedding. -/
theorem solution {n : ℕ} (A : Finset (Fin n))
    (x : EuclideanSpace ℂ (Qubits n)) :
    (compiler_single_majority_query n).queryCount 0 = 1 ∧
    ‖compiler_phase_lift x‖ = ‖x‖ ∧
    ∀ y : Qubits (n+1),
      act ((compiler_single_majority_query n).unitary (fun _ => majorityOracle A))
        (compiler_phase_lift x) y =
      (if majorityBit A (fun i => y i.castSucc) then (-1 : ℂ) else 1) *
        compiler_phase_lift x y := by
  refine ⟨compiler_single_majority_query_count n, compiler_phase_lift_norm x, ?_⟩
  intro y
  rw [compiler_single_majority_query_unitary]
  exact compiler_majority_phase_kickback A x y

/- The phase-kickback encoding is a complex-linear isometry, so arbitrary
unitaries on the data register can be transported through it. -/
noncomputable def compiler_phase_embedding (n : ℕ) :
    EuclideanSpace ℂ (Qubits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Qubits (n+1)) where
  toFun := compiler_phase_lift
  map_add' x y := by
    ext z
    simp [compiler_phase_lift, mul_add]
  map_smul' r x := by
    ext z
    simp [compiler_phase_lift, mul_left_comm]
  norm_map' := compiler_phase_lift_norm

