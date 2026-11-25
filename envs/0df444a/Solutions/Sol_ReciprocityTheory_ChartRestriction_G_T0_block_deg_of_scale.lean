-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.block_deg_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:17.857264+00:00
-- url     : https://prove2.me/submissions/ed47e993-ebf2-4573-b1f9-5e11a60ec9f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeff_scaleEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sum_filter_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution [CharZero K] (b : Fin (D + 1)) (a : ℕ) (F : MvPolynomial (TVar D N) K)
    (hF : ∀ u : Kˣ, scaleEquiv (fun v : TVar D N => v.1 = b) u F = C ((u : K) ^ a) * F) :
    ∀ s ∈ F.support, ∑ j, s (b, j) = a := by
  intro s hs
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have h := congrArg (coeff s) (hF (Units.mk0 2 h2))
  rw [coeff_scaleEquiv, coeff_C_mul, sum_filter_block] at h
  have hc : coeff s F ≠ 0 := mem_support_iff.1 hs
  have h' := mul_right_cancel₀ hc h
  simp only [Units.val_mk0] at h'
  have h'' : ((2 ^ (∑ j, s (b, j)) : ℕ) : K) = ((2 ^ a : ℕ) : K) := by
    push_cast
    exact h'
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h'')
end ReciprocityTheory.ChartRestriction.G.T0
