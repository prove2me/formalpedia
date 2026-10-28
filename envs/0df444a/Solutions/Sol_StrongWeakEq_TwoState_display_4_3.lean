-- Prove2me | solution 1 for StrongWeakEq.TwoState.display_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:34:46.411779+00:00
-- url     : https://prove2.me/submissions/7e97264d-2bbd-4810-91df-73697c80cebe

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel

open Matrix

namespace Aux_SWE43
open StrongWeakEq.TwoState

lemma exp_gen (a b t : ℝ) (hs : 0 < a + b) :
    NormedSpace.exp (t • gen a b) =
      !![(b + a * Real.exp (-(a + b) * t)) / (a + b), (a - a * Real.exp (-(a + b) * t)) / (a + b);
         (b - b * Real.exp (-(a + b) * t)) / (a + b), (a + b * Real.exp (-(a + b) * t)) / (a + b)] := by
  have hs' : a + b ≠ 0 := hs.ne'
  set U : Matrix (Fin 2) (Fin 2) ℝ := !![1, a; 1, -b] with hU
  set V : Matrix (Fin 2) (Fin 2) ℝ := !![b / (a + b), a / (a + b); 1 / (a + b), -1 / (a + b)] with hV
  have hUV : U * V = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hU, hV, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hinv : U⁻¹ = V := Matrix.inv_eq_right_inv hUV
  have hunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_right_inverse hUV)
  have hdecomp : t • gen a b = U * diagonal ![0, -(a + b) * t] * U⁻¹ := by
    rw [hinv]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hU, hV, gen, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal] <;> field_simp <;> ring
  rw [hdecomp, Matrix.exp_conj U _ hunit, Matrix.exp_diagonal, Pi.exp_def, hinv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hU, hV, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal, ← Real.exp_eq_exp_ℝ] <;> field_simp <;> ring


open MeasureTheory

lemma ie (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0:ℝ), Real.exp (-c * t) = 1 / c := by
  refine ⟨integrableOn_exp_mul_Ioi (by linarith) 0, ?_⟩
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp

lemma key (u v ρ ρ' a b : ℝ) (hρ : 0 < ρ) (hρ' : 0 < ρ') (ha : 0 ≤ a) (hb : 0 ≤ b)
    (dd : ℝ → ℝ) (hdd : ∀ t, dd t = u * Real.exp (-ρ * t) + v * Real.exp (-ρ' * t)) (A B : ℝ) :
    (∫ t in Set.Ioi (0:ℝ), ∑ j, NormedSpace.exp (t • gen a b) 0 j * (dd t * (if j = 0 then A else B)))
      - (∫ t in Set.Ioi (0:ℝ), ∑ j, NormedSpace.exp (t • gen a b) 1 j * (dd t * (if j = 0 then A else B)))
      = (u / (ρ + a + b) + v / (ρ' + a + b)) * (A - B) := by
  have hD : IntegrableOn dd (Set.Ioi 0) := by
    have : dd = fun t => u * Real.exp (-ρ * t) + v * Real.exp (-ρ' * t) := funext hdd
    rw [this]
    exact ((ie ρ hρ).1.const_mul u).add ((ie ρ' hρ').1.const_mul v)
  have hDi : ∫ t in Set.Ioi (0:ℝ), dd t = u / ρ + v / ρ' := by
    have : dd = fun t => u * Real.exp (-ρ * t) + v * Real.exp (-ρ' * t) := funext hdd
    rw [this, integral_add ((ie ρ hρ).1.const_mul u) ((ie ρ' hρ').1.const_mul v),
      integral_const_mul, integral_const_mul, (ie ρ hρ).2, (ie ρ' hρ').2]
    ring
  by_cases hs : 0 < a + b
  · set s := a + b with hsdef
    have hD2f : ∀ t, dd t * Real.exp (-s * t) =
        u * Real.exp (-(ρ + s) * t) + v * Real.exp (-(ρ' + s) * t) := by
      intro t
      rw [hdd, add_mul, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hD2 : IntegrableOn (fun t => dd t * Real.exp (-s * t)) (Set.Ioi 0) := by
      have : (fun t => dd t * Real.exp (-s * t)) =
          fun t => u * Real.exp (-(ρ + s) * t) + v * Real.exp (-(ρ' + s) * t) := funext hD2f
      rw [this]
      exact ((ie _ (by linarith)).1.const_mul u).add ((ie _ (by linarith)).1.const_mul v)
    have hD2i : ∫ t in Set.Ioi (0:ℝ), dd t * Real.exp (-s * t) = u / (ρ + s) + v / (ρ' + s) := by
      have : (fun t => dd t * Real.exp (-s * t)) =
          fun t => u * Real.exp (-(ρ + s) * t) + v * Real.exp (-(ρ' + s) * t) := funext hD2f
      rw [this, integral_add ((ie _ (by linarith)).1.const_mul u)
        ((ie _ (by linarith)).1.const_mul v), integral_const_mul, integral_const_mul,
        (ie _ (by linarith)).2, (ie _ (by linarith)).2]
      ring
    have h0 : (fun t : ℝ => ∑ j, NormedSpace.exp (t • gen a b) 0 j * (dd t * (if j = 0 then A else B)))
        = fun t => (b * A + a * B) / s * dd t + (a * A - a * B) / s * (dd t * Real.exp (-s * t)) := by
      funext t
      rw [exp_gen a b t hs, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, if_true, Fin.one_eq_zero_iff,
        one_ne_zero, if_false, hsdef]
      field_simp
      ring
    have h1 : (fun t : ℝ => ∑ j, NormedSpace.exp (t • gen a b) 1 j * (dd t * (if j = 0 then A else B)))
        = fun t => (b * A + a * B) / s * dd t + (-(b * A) + b * B) / s * (dd t * Real.exp (-s * t)) := by
      funext t
      rw [exp_gen a b t hs, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, if_true, Fin.one_eq_zero_iff,
        one_ne_zero, if_false, hsdef]
      field_simp
      ring
    rw [h0, h1, integral_add (hD.const_mul _) (hD2.const_mul _),
      integral_add (hD.const_mul _) (hD2.const_mul _)]
    simp only [integral_const_mul]
    rw [hD2i, hsdef]
    have h3 : ρ + (a + b) ≠ 0 := by linarith
    have h4 : ρ' + (a + b) ≠ 0 := by linarith
    have h5 : ρ + a + b = ρ + (a + b) := by ring
    have h6 : ρ' + a + b = ρ' + (a + b) := by ring
    have h7 : a + b ≠ 0 := by linarith
    rw [h5, h6]
    field_simp
    ring
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    have hg : gen 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [gen]
    simp only [hg, smul_zero, NormedSpace.exp_zero, Fin.sum_univ_two, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), one_mul, zero_mul, add_zero, zero_add,
      if_true, Fin.one_eq_zero_iff, one_ne_zero, if_false]
    rw [integral_mul_const, integral_mul_const, hDi]
    ring

end Aux_SWE43

open StrongWeakEq.TwoState in
theorem solution (lam ρ ρ' : ℝ) (hlam : 0 < lam ∧ lam < 1) (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (g₁ g₂ : ℝ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen a b) 0
        - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen a b) 1
      = (lam / (ρ + a + b) + (1 - lam) / (ρ' + a + b)) * (g₁ a - g₂ b) ∧
    StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen a b) 0
        - StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen a b) 1
      = -(ρ * lam / (ρ + a + b) + ρ' * (1 - lam) / (ρ' + a + b)) * (g₁ a - g₂ b) := by
  have hg01 : gen a b 0 1 = a := by simp [gen]
  have hg10 : gen a b 1 0 = b := by simp [gen]
  have hc : ∀ (dd : ℝ → ℝ) (t : ℝ) (j : Fin 2),
      dd t * (if j = 0 then g₁ (gen a b j 1) else g₂ (gen a b j 0)) =
        dd t * (if j = 0 then g₁ a else g₂ b) := by
    intro dd t j
    fin_cases j
    · simp [hg01]
    · simp [hg10]
  constructor
  · unfold StrongWeakEq.Existence.payoff
    simp only [twoStatePayoff, hc]
    exact Aux_SWE43.key lam (1 - lam) ρ ρ' a b hρ hρ' ha hb (discount lam ρ ρ')
      (fun t => rfl) (g₁ a) (g₂ b)
  · unfold StrongWeakEq.Existence.payoffDeriv
    simp only [twoStatePayoffDeriv, hc]
    rw [Aux_SWE43.key (-ρ * lam) (-ρ' * (1 - lam)) ρ ρ' a b hρ hρ' ha hb (discountDeriv lam ρ ρ')
      (fun t => by unfold discountDeriv; ring) (g₁ a) (g₂ b)]
    ring
