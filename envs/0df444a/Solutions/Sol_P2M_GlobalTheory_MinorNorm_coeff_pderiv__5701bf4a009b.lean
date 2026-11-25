-- Prove2me | solution 1 for P2M_GlobalTheory_MinorNorm_coeff_pderiv__5701bf4a009b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:40.259743+00:00
-- url     : https://prove2.me/submissions/f20f790f-a2e1-4948-995d-d91dcced44a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {σ : Type}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (v : σ) (m : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    (pderiv v Q).coeff m = Q.coeff (m + Finsupp.single v 1) * (m v + 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => simp only [map_add, coeff_add, h₁, h₂, add_mul]
  | monomial b c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : b = m + Finsupp.single v 1
    · subst h; simp
    · rw [if_neg h, zero_mul]
      split_ifs with h'
      · have : b v = 0 := by
          by_contra hb
          apply h
          rw [← h', tsub_add_cancel_of_le]
          rw [Finsupp.single_le_iff]; omega
        simp [this]
      · rfl
end GlobalTheory.MinorNorm
