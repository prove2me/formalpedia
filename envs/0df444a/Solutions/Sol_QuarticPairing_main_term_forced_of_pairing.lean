-- Prove2me | solution 1 for QuarticPairing.main_term_forced_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:47.305419+00:00
-- url     : https://prove2.me/submissions/5bc0f62d-f768-4989-9b4c-ed75dd9cd9f9

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
public import Theorems.Thm_QuarticPairing_isBigO_neg_mul_conj
public import Theorems.Thm_QuarticPairing_eq_zero_of_isBigO
public import Theorems.Thm_QuarticPairing_twistedSum_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b b' : ℂ)
    (h0 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 0 -
      b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)))
    (h1 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 1 -
      b' * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    b' = -κ * starRingEnd ℂ b := by
  have he : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
  have a0 := h0 (1 / 8) (by norm_num)
  have a1 := h1 (1 / 8) (by norm_num)
  rw [he] at a0 a1
  have hs := (a1.neg_left.add (isBigO_neg_mul_conj hκ a0))
  have hz : b' + κ * starRingEnd ℂ b = 0 := by
    refine eq_zero_of_isBigO (hs.congr_left fun X => ?_)
    rw [twistedSum_one g Λ β hκ h12 X, map_sub, map_mul, Complex.conj_ofReal]
    ring
  linear_combination hz
end QuarticPairing
