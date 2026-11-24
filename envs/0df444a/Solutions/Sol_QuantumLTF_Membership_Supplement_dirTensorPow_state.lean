-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.dirTensorPow_state
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T19:35:01.618362+00:00
-- url     : https://prove2.me/submissions/bb38a862-0401-4119-b8aa-468d27b1e2a4

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_IsStateOnSpan
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
import Definitions.Def_QuantumLTF_Membership_flatReg

set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped ComplexOrder

theorem section5_encoding_injective {n s : ℕ} (h : n ≤ 2^s) :
    Function.Injective (fun i : Fin n => natToBits s i) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg (bitsEquivFin s) hij
  have hi : (i : ℕ) < 2^s := lt_of_lt_of_le i.isLt h
  have hj : (j : ℕ) < 2^s := lt_of_lt_of_le j.isLt h
  simpa [natToBits, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using congrArg Fin.val he

theorem section5_dirAmp_at_label {n s : ℕ} (h : n ≤ 2^s)
    (w : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    dirAmp s w (natToBits s i) = (w i : ℂ) := by
  classical
  simp only [dirAmp, (section5_encoding_injective h).eq_iff]
  simp

theorem section5_dirAmp_star {n s : ℕ} (w : EuclideanSpace ℝ (Fin n)) (b : Qubits s) :
    star (dirAmp s w b) = dirAmp s w b := by
  classical
  simp only [dirAmp, star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem section5_dirAmp_sq_sum {n s : ℕ} (h : n ≤ 2^s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    ∑ b : Qubits s, dirAmp s w b * dirAmp s w b = 1 := by
  classical
  calc
    ∑ b : Qubits s, dirAmp s w b * dirAmp s w b =
        ∑ b : Qubits s, ∑ i : Fin n,
          if b = natToBits s i then (w i : ℂ) * dirAmp s w b else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [dirAmp, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp_all
    _ = ∑ i : Fin n, ∑ b : Qubits s,
          if b = natToBits s i then (w i : ℂ) * dirAmp s w b else 0 :=
      Finset.sum_comm
    _ = ∑ i : Fin n, (w i : ℂ) * (w i : ℂ) := by
      simp [section5_dirAmp_at_label h]
    _ = 1 := by
      have hsq := EuclideanSpace.norm_sq_eq w
      simp only [hw, one_pow, Real.norm_eq_abs, sq_abs] at hsq
      have hh : ∑ i : Fin n, (w i)^2 = 1 := hsq.symm
      simpa [pow_two] using (show (∑ i : Fin n, (w i : ℂ)^2) = 1 by exact_mod_cast hh)

noncomputable def section5_register_equiv (K s : ℕ) :
    Qubits (K*s) ≃ (Fin K → Qubits s) where
  toFun := splitReg K s
  invFun := flatReg K s
  left_inv y := by
    funext j
    change y (finProdFinEquiv (finProdFinEquiv.symm j)) = y j
    rw [Equiv.apply_symm_apply]
  right_inv y := by
    funext i j
    simp [flatReg, splitReg]

theorem section5_dirTensorPow_trace {n s K : ℕ} (h : n ≤ 2^s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    (dirTensorPow s K w).trace = 1 := by
  classical
  change (∑ y : Qubits (K*s),
    ∏ k : Fin K, dirAmp s w (splitReg K s y k) * dirAmp s w (splitReg K s y k)) = 1
  calc
    _ = ∑ z : Fin K → Qubits s, ∏ k : Fin K, dirAmp s w (z k) * dirAmp s w (z k) :=
      Fintype.sum_equiv (section5_register_equiv K s)
        (fun y => ∏ k : Fin K, dirAmp s w (splitReg K s y k) * dirAmp s w (splitReg K s y k))
        (fun z => ∏ k : Fin K, dirAmp s w (z k) * dirAmp s w (z k)) (fun _ => rfl)
    _ = 1 := by
      rw [← Fintype.prod_sum (fun (_ : Fin K) (b : Qubits s) => dirAmp s w b * dirAmp s w b)]
      simp [section5_dirAmp_sq_sum h w hw]

theorem section5_dirTensorPow_posSemidef {n s K : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) : (dirTensorPow s K w).PosSemidef := by
  classical
  let A : Matrix (Qubits (K*s)) (Fin 1) ℂ :=
    fun y _ => ∏ k : Fin K, dirAmp s w (splitReg K s y k)
  have heq : dirTensorPow s K w = A * A.conjTranspose := by
    ext y z
    change (∏ k : Fin K, dirAmp s w (splitReg K s y k) *
      dirAmp s w (splitReg K s z k)) =
      ∑ j : Fin 1, A y j * star (A z j)
    simp [A, Finset.prod_mul_distrib, section5_dirAmp_star]
  rw [heq]
  exact Matrix.posSemidef_self_mul_conjTranspose A

theorem section5_dirAmp_support {n s : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (b : Qubits s) (h : dirAmp s w b ≠ 0) : ∃ i : Fin n, b = natToBits s i := by
  classical
  by_contra hn
  push_neg at hn
  exact h (by simp [dirAmp, hn])

theorem solution {n s K : ℕ} (h : n ≤ 2^s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    IsStateOnSpan n s K (dirTensorPow s K w) := by
  classical
  refine ⟨section5_dirTensorPow_posSemidef w, section5_dirTensorPow_trace h w hw, ?_⟩
  intro y z hyz
  change (∏ k : Fin K, dirAmp s w (splitReg K s y k) *
    dirAmp s w (splitReg K s z k)) ≠ 0 at hyz
  have hall := Finset.prod_ne_zero_iff.mp hyz
  constructor
  · intro k
    exact section5_dirAmp_support w _ (mul_ne_zero_iff.mp (hall k (Finset.mem_univ k))).1
  · intro k
    exact section5_dirAmp_support w _ (mul_ne_zero_iff.mp (hall k (Finset.mem_univ k))).2
