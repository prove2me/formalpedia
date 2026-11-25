-- Prove2me | solution 1 for QuarticPairing.mul_conj_eq_neg_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:35:48.13902+00:00
-- url     : https://prove2.me/submissions/76aa1df0-28e8-44fe-8615-c5bc11864cf6

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_mul_conj_self_eq_one

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {g θ κ : ℂ} (hθ : ‖θ‖ = 1) (hκ : ‖κ‖ = 1)
    (h : g = 0 ∨ g ^ 2 = -κ * θ) : g * starRingEnd ℂ θ = -κ * starRingEnd ℂ g := by
  rcases h with h | h
  · simp [h]
  · have hκκ := mul_conj_self_eq_one hκ
    have hθ' : θ = -g ^ 2 * starRingEnd ℂ κ := by
      linear_combination (starRingEnd ℂ κ) * h - θ * hκκ
    have hn : ‖g‖ ^ 2 = 1 := by
      have := congrArg norm hθ'
      rw [hθ, norm_mul, norm_neg, norm_pow, Complex.norm_conj, hκ, mul_one] at this
      exact this.symm
    have hgg : g * starRingEnd ℂ g = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    rw [hθ', map_mul, map_neg, map_pow, Complex.conj_conj]
    linear_combination (-(κ * starRingEnd ℂ g)) * hgg
end QuarticPairing
