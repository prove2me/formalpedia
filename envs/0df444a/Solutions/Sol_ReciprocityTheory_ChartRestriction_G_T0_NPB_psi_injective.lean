-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.psi_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:31.3808+00:00
-- url     : https://prove2.me/submissions/c7166ae0-cff4-44ab-a603-fa35539dbbb6

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_homog_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_homog_coeff_isMH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0) :
    Function.Injective (psi sg tt) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  apply homog_injective (K := K) (D := D) (N := N)
  rw [map_zero]
  refine MvPolynomial.ext _ _ fun γ => ?_
  rw [coeff_zero]
  by_contra hne
  have h0 : coeff γ (psi sg tt q) = 0 := by rw [hq, coeff_zero]
  rw [psi, RingHom.comp_apply, coeff_map] at h0
  exact hG _ _ (homog_coeff_isMH q γ) hne (by simpa using h0)
end ReciprocityTheory.ChartRestriction.G.T0.NPB
