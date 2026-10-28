-- Prove2me | solution 1 for PersonalizedAssortment.IB.dual_certificate_feasible
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:21.669164+00:00
-- url     : https://prove2.me/submissions/8a56ee62-e514-404f-b3b9-cea234b125cb

import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open scoped BigOperators
open Finset PersonalizedAssortment.IB

theorem solution {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (c : Fin n → ℕ) (hc : ∀ i, 0 < c i) (𝒮 : Finset (Finset (Fin n))) (h𝒮 : ∅ ∈ 𝒮)
    (φ : Z → ChoiceModel n) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (hsel : IsIBRule Ψ r c 𝒮 φ z sel)
    (I : ℕ → Fin n → ℕ) (hI0 : I 0 = c) (hmono : ∀ t < T, ∀ i, I (t + 1) i ≤ I t i) :
    DualFeasible r 𝒮 φ z (fun t => lamIB Ψ r c φ z sel t (I t.val)) (thetaIB Ψ r c (I T)) := by
  classical
  have hdec : ∀ b, b ≤ T → ∀ a, a ≤ b → ∀ i, I b i ≤ I a i := by
    intro b
    induction b with
    | zero =>
        intro hb a ha i
        have : a=0 := Nat.eq_zero_of_le_zero ha
        subst a; exact le_rfl
    | succ b ih =>
        intro hb a ha i
        rcases Nat.le_succ_iff.mp ha with hab|rfl
        · exact (hmono b (Nat.lt_of_succ_le hb) i).trans (ih (Nat.le_of_succ_le hb) a hab i)
        · exact le_rfl
  have hcap : ∀ t, t ≤ T → ∀ i,I t i ≤ c i := by
    intro t ht i
    simpa only [hI0] using hdec t ht 0 (Nat.zero_le _) i
  have hfrac : ∀ t, t ≤ T → ∀ i, (I t i : ℝ)/(c i : ℝ) ∈ Set.Icc 0 1 := by
    intro t ht i
    have hcpos : (0:ℝ)<c i := Nat.cast_pos.mpr (hc i)
    exact ⟨div_nonneg (Nat.cast_nonneg _) hcpos.le,
      (div_le_one hcpos).mpr (Nat.cast_le.mpr (hcap t ht i))⟩
  constructor
  · intro t S hS
    change (∑ i : Fin n,(φ (z t)).prob S i *
      (r i-r i*(1-Ψ ((I T i:ℝ)/(c i:ℝ))))) ≤ ibIndex Ψ r c (φ (z t)) (I t.val) (sel t (I t.val))
    calc
      _ = ∑ i : Fin n, Ψ ((I T i:ℝ)/(c i:ℝ))*r i*(φ (z t)).prob S i := by
        apply sum_congr rfl; intro i _; ring
      _ ≤ ∑ i : Fin n, Ψ ((I t.val i:ℝ)/(c i:ℝ))*r i*(φ (z t)).prob S i := by
        apply sum_le_sum; intro i _
        have hmonoΨ := hΨ.2.1 (hfrac T le_rfl i) (hfrac t.val t.isLt.le i)
          (div_le_div_of_nonneg_right (Nat.cast_le.mpr (hdec T le_rfl t.val t.isLt.le i)) (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmonoΨ (hr i).le) ((φ (z t)).prob_nonneg S i)
      _ = ibIndex Ψ r c (φ (z t)) (I t.val) S := by
        unfold ibIndex
        symm
        apply sum_subset (subset_univ S)
        intro i _ hi
        rw [(φ (z t)).prob_eq_zero_of_not_mem S i hi,mul_zero]
      _ ≤ _ := (hsel t (I t.val)).2.1 S hS
  · intro i
    exact mul_nonneg (hr i).le (sub_nonneg.mpr (hΨ.1 (hfrac T le_rfl i)).2)

#print axioms solution

