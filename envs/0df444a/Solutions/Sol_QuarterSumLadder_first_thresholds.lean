-- Prove2me | solution 1 for QuarterSumLadder.first_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:38.374575+00:00
-- url     : https://prove2.me/submissions/8add89e4-cf08-45d8-b0df-aebb78c09bc5

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
public import Theorems.Thm_QuarterSumLadder_norm_eq
public import Theorems.Thm_QuarterSumLadder_coord_parity
public import Theorems.Thm_QuarterSumLadder_even_even_eight
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_odd


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution :
    (χ 2 = -1 → (2 : ℤ) ∣ (Omega χ).norm ∧ ¬ (4 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (4 : ℤ) ∣ (Omega χ).norm ∧ ¬ (8 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (8 : ℤ) ∣ (Omega χ).norm) := by
  obtain ⟨hodd, heven⟩ := coord_parity hp8 hχ
  have hpq := mod_eight_aux hp8
  rw [norm_eq]
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 => ?_⟩
  · obtain ⟨hx, hy⟩ := hodd hw
    have := sq_add_sq_odd hx hy
    omega
  · obtain ⟨hx, hy, hxy⟩ := heven hw
    obtain ⟨h4, h8⟩ := even_even_eight hx hy
    refine ⟨h4, fun h => ?_⟩
    have := h8.1 h
    have hQ : (Q p : ℤ) % 4 = 2 := by unfold Q; omega
    omega
  · obtain ⟨hx, hy, hxy⟩ := heven hw
    obtain ⟨_, h8⟩ := even_even_eight hx hy
    refine h8.2 ?_
    have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
    omega
end QuarterSumLadder
