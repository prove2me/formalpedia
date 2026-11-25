-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.bf_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:02.637352+00:00
-- url     : https://prove2.me/submissions/95eb9ec2-0de0-410d-812d-8bbeb83b0f3c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_induction
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_add_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_add_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreC PositivityTheory.Rg.Sw.LC.CoreC.G
variable {τ : Type} [Fintype τ] [DecidableEq τ]
variable (w : (τ →₀ ℕ) → ℂ)
variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw
omit hw
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (k : τ) (p q : MvPolynomial τ ℂ) : bf w (X k * p) q = κ * bf w p (pderiv k q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, bf_monomial, bf_monomial]
    by_cases h : Finsupp.single k 1 + s = t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _).symm, hw]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [if_neg h]
      by_cases h' : s = t - Finsupp.single k 1
      · rw [if_pos h']
        have : t k = 0 := by
          by_contra h0
          apply h
          rw [h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [mul_add, bf_add_left, bf_add_left, h1, h2, mul_add]
  · rw [bf_add_right, map_add, bf_add_right, h1, h2, mul_add]
end PositivityTheory.Rg.Sw.LC.CoreC.G
