-- Prove2me | solution 1 for QuarticPairing.term_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:32.521071+00:00
-- url     : https://prove2.me/submissions/4093141a-4f5e-4b03-b1b7-2039d57ea001

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_mul_conj_eq_neg_conj
public import Theorems.Thm_QuarticPairing_norm_unitDir
public import Theorems.Thm_QuarticPairing_unitDir_zero

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {g κ : ℂ} (hκ : ‖κ‖ = 1) {c : GaussianInt}
    (h : g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) = -κ * starRingEnd ℂ g := by
  by_cases hc : c = 0
  · subst hc
    rw [unitDir_zero] at h ⊢
    rcases h with h | h
    · simp [h]
    · have : g = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by simpa using h)
      simp [this]
  · exact mul_conj_eq_neg_conj (norm_unitDir hc) hκ h
end QuarticPairing
