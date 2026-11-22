-- Prove2me | solution 1 for SupplierLearning.claim_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:35:40.775507+00:00
-- url     : https://prove2.me/submissions/ba20614f-3d69-4303-8d2a-8744657eb3eb

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_Feasible
import Definitions.Def_SupplierLearning_Params_rentBound

set_option autoImplicit false

open SupplierLearning

theorem solution (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ)
    (hq : 0 < (φ .h).q₁) :
    let q := (φ .h).q₁
    let y := (φ .h).q₂ true
    let z := (φ .h).q₂ false
    let x := y - z
    let D := (φ .h).p₂ true - (φ .h).p₂ false
    (P.ch - P.rh * q) * x ≤ D ∧ D ≤ P.ch * x ∧
    P.supplierPayoff φ .l .h - P.U φ .h =
      P.deltaC * q + P.δ * P.ρ * (P.deltaC + P.deltaR * q) * y +
        P.δ * (1 - P.ρ) * (P.deltaC * z + max 0 (D - P.cl * x)) ∧
    P.rentBound q y z ≤ P.supplierPayoff φ .l .h - P.U φ .h ∧
    (D = (P.ch - P.rh * q) * x → P.supplierPayoff φ .l .h - P.U φ .h = P.rentBound q y z) := by
  dsimp only
  have ic1 := hφ.ic_outcome .h true false
  have ic2 := hφ.ic_outcome .h false true
  have hcap := hφ.capacity .h
  have hrh := hP.rh_pos
  have hδ := hP.δ_pos
  have hρ := hP.ρ_lt_one
  simp only [Params.U, Params.supplierPayoff, Params.expectOutcome, Params.stagePayoff,
    Params.learnedCost, Params.cost, Params.rate, outcomeValue, Params.rentBound,
    Params.rentFloor, Params.deltaC, Params.deltaR, mul_one, mul_zero, sub_zero] at ic1 ic2 ⊢
  generalize (φ SupplierType.h).p₂ true = P1 at *
  generalize (φ SupplierType.h).p₂ false = P0 at *
  generalize (φ SupplierType.h).q₂ true = y at *
  generalize (φ SupplierType.h).q₂ false = z at *
  generalize (φ SupplierType.h).q₁ = q at *
  generalize (φ SupplierType.h).p₁ = p1 at *
  have hx : 0 ≤ y - z := by
    have h1 : 0 ≤ P.rh * q * (y - z) := by linarith
    exact (mul_nonneg_iff_of_pos_left (mul_pos hrh hq)).mp h1
  have il1 : P0 - (P.cl - P.rl * q) * z ≤ P1 - (P.cl - P.rl * q) * y := by
    have hk : 0 ≤ (P.ch - P.cl + (P.rl - P.rh) * q) * (y - z) := mul_nonneg (by linarith) hx
    linarith
  have hmax : ∀ a b : ℝ, max a b = a + max 0 (b - a) := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
      ring
  have harg : P1 - P.cl * y - (P0 - P.cl * z) = P1 - P0 - P.cl * (y - z) := by ring
  have key : p1 - P.cl * q +
        P.δ * (P.ρ * max (P0 - (P.cl - P.rl * q) * z) (P1 - (P.cl - P.rl * q) * y) +
          (1 - P.ρ) * max (P0 - P.cl * z) (P1 - P.cl * y)) -
      (p1 - P.ch * q +
        P.δ * (P.ρ * max (P0 - (P.ch - P.rh * q) * z) (P1 - (P.ch - P.rh * q) * y) +
          (1 - P.ρ) * max (P0 - P.ch * z) (P1 - P.ch * y))) =
      (P.ch - P.cl) * q + P.δ * P.ρ * (P.ch - P.cl + (P.rl - P.rh) * q) * y +
        P.δ * (1 - P.ρ) * ((P.ch - P.cl) * z + max 0 (P1 - P0 - P.cl * (y - z))) := by
    rw [max_eq_right ic1, max_eq_left ic2, max_eq_right il1, hmax (P0 - P.cl * z), harg]
    ring
  refine ⟨by linarith, by linarith, key, ?_, ?_⟩
  · rw [key]
    have hM : max 0 ((P.ch - P.cl - P.rh * q) * (y - z)) ≤ max 0 (P1 - P0 - P.cl * (y - z)) :=
      max_le_max le_rfl (by linarith)
    have hw : 0 ≤ P.δ * (1 - P.ρ) := mul_nonneg hδ.le (by linarith)
    have := mul_le_mul_of_nonneg_left hM hw
    linarith
  · intro hD
    rw [key]
    have : P1 - P0 - P.cl * (y - z) = (P.ch - P.cl - P.rh * q) * (y - z) := by
      rw [hD]
      ring
    rw [this]
    ring
