-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.binaryVariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:13:34.271343+00:00
-- url     : https://prove2.me/submissions/8b541b29-ca00-4f4d-b615-08ab47e59e88

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators

private lemma bool_sum_succ (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    (∑ z, f z) = (∑ z : Fin n → Bool, f (Fin.cons false z)) +
      (∑ z : Fin n → Bool, f (Fin.cons true z)) := by
  let e : (Bool × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) :=
    { toFun := fun z => Fin.cons z.1 z.2
      invFun := fun z => (z 0, fun i => z i.succ)
      left_inv := by intro z; simp
      right_inv := by intro z; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  rw [← Fintype.sum_equiv e (fun z => f (e z)) f (fun _ => rfl)]
  simp [Fintype.sum_prod_type, e, add_comm]

private lemma mass (p : ℝ) (n : ℕ) :
    (∑ z : Fin n → Bool, ∏ i, (if z i then p else 1-p)) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then p else 1-p)]
  simp

private lemma centered (p : ℝ) (n : ℕ) :
    (∑ z : Fin n → Bool, (∏ i, (if z i then p else 1-p)) *
      (∑ i, ((if z i then (1:ℝ) else -1) - (2*p-1)))^2) =
        (n:ℝ) * (1-(2*p-1)^2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bool_sum_succ]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Bool.false_eq_true, ↓reduceIte]
    rw [← Finset.sum_add_distrib]
    simp_rw [show ∀ (W S : ℝ), (1-p)*W*(-1-(2*p-1)+S)^2 +
      p*W*(1-(2*p-1)+S)^2 = W*S^2 + (1-(2*p-1)^2)*W by intros; ring]
    rw [Finset.sum_add_distrib, ih, ← Finset.mul_sum, mass]
    push_cast
    ring

theorem solution (p C : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hC : 0 < C)
    (R R0 : ℕ) (hR : 0 < R) (hR0 : 0 < R0)
    (idealRange : |C*(2*p-1)| ≤ 1) :
    let weight : Bool → ℝ := fun b => if b then p else 1-p
    let value : Bool → ℝ := fun b => if b then 1 else -1
    let m := C*(2*p-1)
    let mean : (Fin R → Bool) → ℝ := fun z => C/(R : ℝ)*∑ i, value (z i)
    (∑ z : Fin R → Bool, (∏ i, weight (z i)) * (mean z-m)^2) =
      (C^2-m^2)/(R : ℝ) ∧
    Real.sqrt ((C^2-m^2)/(R : ℝ)) ≤ C/Real.sqrt R ∧
    (|m| < 1 →
      (((C^2-m^2)/(R : ℝ) = (1-m^2)/(R0 : ℝ)) ↔
        (R : ℝ)/(R0 : ℝ) = (C^2-m^2)/(1-m^2))) := by
  dsimp only
  have hr : (0:ℝ) < R := by exact_mod_cast hR
  have hr0 : (0:ℝ) < R0 := by exact_mod_cast hR0
  have hrn := ne_of_gt hr
  have hr0n := ne_of_gt hr0
  refine ⟨?_, ?_, ?_⟩
  · have hn (z : Fin R → Bool) :
        C/(R:ℝ)*(∑ i, (if z i then (1:ℝ) else -1)) - C*(2*p-1) =
        C/(R:ℝ)*(∑ i, ((if z i then (1:ℝ) else -1)-(2*p-1))) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simp_rw [hn, mul_pow]
    simp_rw [show ∀ W S : ℝ, W*((C/(R:ℝ))^2*S) = (C/(R:ℝ))^2*(W*S) by intros; ring]
    rw [← Finset.mul_sum, centered]
    field_simp
  · calc
      Real.sqrt ((C^2-(C*(2*p-1))^2)/(R:ℝ)) ≤ Real.sqrt (C^2/(R:ℝ)) := by
        apply Real.sqrt_le_sqrt
        exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (le_of_lt hr)
      _ = C/Real.sqrt (R:ℝ) := by rw [Real.sqrt_div (sq_nonneg C), Real.sqrt_sq (le_of_lt hC)]
  · intro hm
    have hd : 0 < 1-(C*(2*p-1))^2 := by
      have := (abs_lt.mp hm)
      nlinarith
    rw [div_eq_div_iff hrn hr0n, div_eq_div_iff hr0n (ne_of_gt hd)]
    constructor <;> intro h <;> nlinarith [h]
