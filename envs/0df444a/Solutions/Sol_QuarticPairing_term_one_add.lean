-- Prove2me | solution 1 for QuarticPairing.term_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:21.145282+00:00
-- url     : https://prove2.me/submissions/b2d4a9a9-125d-4ed7-8a37-fe0a74ada2ca

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_term_pairing

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g κ : ℂ) (hκ : ‖κ‖ = 1) (c : GaussianInt) (Λ : ℝ)
    (h : Λ ≠ 0 → g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) ^ (1 : ℤ) * (Λ : ℂ) +
      κ * starRingEnd ℂ (g * starRingEnd ℂ (unitDir c) ^ (0 : ℤ) * (Λ : ℂ)) = 0 := by
  by_cases hΛ : Λ = 0
  · simp [hΛ]
  · rw [zpow_one, zpow_zero, mul_one, term_pairing hκ (h hΛ), map_mul, Complex.conj_ofReal]
    ring
end QuarticPairing
