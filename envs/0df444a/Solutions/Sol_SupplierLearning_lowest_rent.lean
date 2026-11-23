-- Prove2me | solution 1 for SupplierLearning.lowest_rent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:10:52.648148+00:00
-- url     : https://prove2.me/submissions/528517cd-e99d-4506-b3ca-88c8a1257183

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_Feasible
import Definitions.Def_SupplierLearning_Params_buyerPayoff
import Definitions.Def_SupplierLearning_Params_typeSurplus
import Definitions.Def_SupplierLearning_Params_rentBound

set_option autoImplicit false

open SupplierLearning

namespace SupplierLearning.LowestRentProof

theorem rent_lb (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ) :
    P.U φ .h + P.rentBound (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false) ≤
      P.supplierPayoff φ .l .h := by
  have ic1 := hφ.ic_outcome .h true false
  have ic2 := hφ.ic_outcome .h false true
  have hδ := hP.δ_pos
  have hρ0 := hP.ρ_pos
  have hρ1 := hP.ρ_lt_one
  simp only [Params.U, Params.supplierPayoff, Params.expectOutcome, Params.stagePayoff,
    Params.learnedCost, Params.cost, Params.rate, outcomeValue, Params.rentBound,
    Params.rentFloor, Params.deltaC, Params.deltaR, mul_one, mul_zero, sub_zero] at ic1 ic2 ⊢
  generalize (φ SupplierType.h).p₂ true = P1 at *
  generalize (φ SupplierType.h).p₂ false = P0 at *
  generalize (φ SupplierType.h).q₂ true = y at *
  generalize (φ SupplierType.h).q₂ false = z at *
  generalize (φ SupplierType.h).q₁ = q at *
  generalize (φ SupplierType.h).p₁ = p1 at *
  rw [max_eq_right ic1, max_eq_left ic2]
  have hl1 : P1 - (P.cl - P.rl * q) * y ≤
      max (P0 - (P.cl - P.rl * q) * z) (P1 - (P.cl - P.rl * q) * y) := le_max_right _ _
  have hmax : ∀ a b : ℝ, max a b = a + max 0 (b - a) := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  have hl0 : P0 - P.cl * z + max 0 ((P.ch - P.cl - P.rh * q) * (y - z)) ≤
      max (P0 - P.cl * z) (P1 - P.cl * y) := by
    rw [hmax (P0 - P.cl * z)]
    have : max 0 ((P.ch - P.cl - P.rh * q) * (y - z)) ≤ max 0 (P1 - P.cl * y - (P0 - P.cl * z)) :=
      max_le_max le_rfl (by linarith)
    linarith
  have w1 : 0 ≤ P.δ * P.ρ := by positivity
  have w2 : 0 ≤ P.δ * (1 - P.ρ) := mul_nonneg hδ.le (by linarith)
  have t1 := mul_le_mul_of_nonneg_left hl1 w1
  have t2 := mul_le_mul_of_nonneg_left hl0 w2
  nlinarith [t1, t2]

theorem U_eq (P : Params) {φ : Contract} (hφ : P.Feasible φ) (θ : SupplierType) :
    P.U φ θ = (φ θ).p₁ - P.cost θ * (φ θ).q₁ +
      P.δ * (P.ρ * ((φ θ).p₂ true - (P.cost θ - P.rate θ * (φ θ).q₁) * (φ θ).q₂ true) +
        (1 - P.ρ) * ((φ θ).p₂ false - P.cost θ * (φ θ).q₂ false)) := by
  have i1 := hφ.ic_outcome θ true false
  have i2 := hφ.ic_outcome θ false true
  simp only [Params.stagePayoff, Params.learnedCost, outcomeValue, mul_one, mul_zero,
    sub_zero] at i1 i2
  simp only [Params.U, Params.supplierPayoff, Params.expectOutcome, Params.stagePayoff,
    Params.learnedCost, outcomeValue, mul_one, mul_zero, sub_zero]
  rw [max_eq_right i1, max_eq_left i2]

end SupplierLearning.LowestRentProof

open SupplierLearning.LowestRentProof in
theorem solution (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ) :
    P.U φ .h + P.rentBound (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false) ≤
      P.supplierPayoff φ .l .h ∧
    P.supplierPayoff φ .l .h ≤ P.U φ .l ∧
    P.buyerPayoff φ ≤
      P.ν * (P.typeSurplus .l (φ .l).q₁ ((φ .l).q₂ true) ((φ .l).q₂ false) -
          P.rentBound (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false)) +
        (1 - P.ν) * P.typeSurplus .h (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false) - P.U φ .h := by
  have h1 := rent_lb P hP hφ
  have h2 : P.supplierPayoff φ .l .h ≤ P.U φ .l := hφ.ic_type .l .h
  refine ⟨h1, h2, ?_⟩
  have hTB : ∀ θ, P.termBuyerPayoff (φ θ) =
      P.typeSurplus θ (φ θ).q₁ ((φ θ).q₂ true) ((φ θ).q₂ false) - P.U φ θ := by
    intro θ
    rw [U_eq P hφ θ]
    simp only [Params.termBuyerPayoff, Params.typeSurplus, Params.expectOutcome]
    ring
  unfold Params.buyerPayoff Params.expectType
  simp only []
  rw [hTB .l, hTB .h]
  have hν := hP.ν_pos
  have := mul_nonneg hν.le (show 0 ≤ P.U φ .l - P.U φ .h -
    P.rentBound (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false) by linarith)
  nlinarith
