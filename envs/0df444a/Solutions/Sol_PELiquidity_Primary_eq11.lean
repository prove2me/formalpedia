-- Prove2me | solution 1 for PELiquidity.Primary.eq11
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:07:40.006772+00:00
-- url     : https://prove2.me/submissions/2d2c1ee4-6580-4694-8b72-75f75ff1c419

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting
open PELiquidity.Primary

theorem solution(lam δ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ Rb : ℝ, (1 - lam) * Rb + lam * (δ * Rb) = 1 ↔ Rb = grossReturn lam δ) ∧
    StrictAntiOn (grossReturn lam) (Set.Ioo 0 1) := by
  have hd : ∀ δ' : ℝ, 0 < δ' → 0 < 1 - lam * (1 - δ') := fun δ' h => by
    nlinarith [mul_pos hlam0 h]
  refine ⟨fun Rb => ?_, ?_⟩
  · have h0 := hd δ hδ0
    unfold grossReturn
    rw [eq_div_iff h0.ne']
    constructor <;> intro h <;> linarith
  · intro x hx y hy hxy
    unfold grossReturn
    apply one_div_lt_one_div_of_lt (hd x hx.1)
    nlinarith [mul_lt_mul_of_pos_left hxy hlam0]
