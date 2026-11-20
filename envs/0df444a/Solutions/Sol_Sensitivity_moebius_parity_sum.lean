-- Prove2me | solution 1 for Sensitivity.moebius_parity_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:00:25.182087+00:00
-- url     : https://prove2.me/submissions/e89aaf6f-3711-4223-9d5f-4a3b91384ad8

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity
import Theorems.Thm_Sensitivity_parity_flipBit
import Theorems.Thm_Sensitivity_boolToInt_false
import Theorems.Thm_Sensitivity_boolToInt_true
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_indicator_not_mem
attribute [local simp] Sensitivity.boolToInt_false
attribute [local simp] Sensitivity.boolToInt_true
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same
attribute [local simp] Sensitivity.indicator_mem
attribute [local simp] Sensitivity.indicator_not_mem


section
namespace Sensitivity
variable {n : ℕ}
private theorem parity_sum_zero (hn : 0 < n) :
    ∑ x : Fin n → Bool, parity x = 0 := by
  have i₀ : Fin n := ⟨0, hn⟩
  -- flipBit · i₀ is a bijection (it's an involution)
  have hbij : Function.Bijective (fun x : Fin n → Bool => flipBit x i₀) :=
    ⟨fun a b h => by
       -- h : flipBit a i₀ = flipBit b i₀ (after beta-reduction)
       have h' : flipBit a i₀ = flipBit b i₀ := h
       calc a = flipBit (flipBit a i₀) i₀ := (flipBit_flipBit_same a i₀).symm
         _ = flipBit (flipBit b i₀) i₀ := by rw [h']
         _ = b := flipBit_flipBit_same b i₀,
     fun y => ⟨flipBit y i₀, flipBit_flipBit_same y i₀⟩⟩
  have h : ∑ x : Fin n → Bool, parity x =
           ∑ x : Fin n → Bool, -parity x := by
    conv_lhs =>
      rw [← Fintype.sum_bijective _ hbij _ _ (fun x => rfl)]
    simp [parity_flipBit]
  linarith [Finset.sum_neg_distrib (f := fun x : Fin n → Bool => parity x)
              (s := Finset.univ)]
private theorem indicator_filter_true (x : Fin n → Bool) :
    indicator (Finset.univ.filter (fun i => x i)) = x := by
  ext i
  simp [indicator]
private theorem filter_true_indicator (T : Finset (Fin n)) :
    Finset.univ.filter (fun i => indicator T i) = T := by
  ext i
  simp [indicator]
end Sensitivity
end

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (f : BoolFun n) (hn : 0 < n) :
    ∑ x : Fin n → Bool, f.paritySigned x =
    2 * (-1 : ℤ) ^ n * f.moebius Finset.univ := by
  -- Step 1: Express paritySigned in terms of boolToInt
  -- f.pmOne x = 2 * boolToInt(f x) - 1
  have pmOne_eq : ∀ x, f.pmOne x = 2 * boolToInt (f x) - 1 := by
    intro x; unfold BoolFun.pmOne boolToInt; split <;> ring
  simp_rw [BoolFun.paritySigned, pmOne_eq, sub_mul, Finset.sum_sub_distrib, one_mul]
  -- LHS = ∑ 2 * boolToInt(f x) * parity x - ∑ parity x
  rw [parity_sum_zero hn, sub_zero]
  -- Goal: ∑ x, 2 * boolToInt (f x) * parity x = 2 * (-1) ^ n * f.moebius univ
  -- Factor out 2 and reduce to the core identity
  suffices h : ∑ x : Fin n → Bool, boolToInt (f x) * parity x =
               (-1 : ℤ) ^ n * f.moebius Finset.univ by
    simp_rw [show ∀ x : Fin n → Bool,
      2 * boolToInt (f x) * parity x = 2 * (boolToInt (f x) * parity x) from
      fun x => by ring]
    rw [← Finset.mul_sum, h]; ring
  -- Now prove: ∑ x, boolToInt(f x) * parity x = (-1)^n * f.moebius univ
  unfold BoolFun.moebius parity
  -- RHS = (-1)^n * ∑ T ∈ univ.powerset, (-1)^(univ.card-T.card) * boolToInt(f(indicator T))
  rw [Finset.mul_sum]
  -- Simplify (-1)^n * (-1)^(univ.card-T.card) = (-1)^T.card
  conv_rhs =>
    arg 2; ext T
    rw [← mul_assoc, ← pow_add, Finset.card_univ, Fintype.card_fin]
    rw [show n + (n - Finset.card T) =
        Finset.card T + 2 * (n - Finset.card T) from by
      have : T.card ≤ n := by
        have := Finset.card_le_univ T
        rwa [Fintype.card_fin] at this
      omega]
    rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  -- Now both sides sum (-1)^card * boolToInt(f ...)
  -- LHS sums over x : Fin n → Bool with card = (filter true x).card
  -- RHS sums over T ∈ univ.powerset with card = T.card
  -- Use the bijection x ↔ (filter true x) / indicator T
  rw [show Finset.univ.powerset = (Finset.univ : Finset (Finset (Fin n))) from by
    ext S; simp]
  -- Now RHS = ∑ T : Finset (Fin n), (-1)^T.card * boolToInt(f(indicator T))
  -- Change the LHS sum using the bijection
  symm
  apply Fintype.sum_equiv
    (Equiv.ofBijective (fun T : Finset (Fin n) => indicator T)
      ⟨fun S T h => by
         have h' : indicator S = indicator T := h
         rw [← filter_true_indicator S, h', filter_true_indicator],
       fun x => ⟨Finset.univ.filter (fun i => x i), indicator_filter_true x⟩⟩)
  intro T
  change (-1 : ℤ) ^ T.card * boolToInt (f (indicator T)) =
    boolToInt (f (indicator T)) * (-1 : ℤ) ^ (Finset.univ.filter (fun i => indicator T i)).card
  rw [filter_true_indicator]
  ring
end Sensitivity
