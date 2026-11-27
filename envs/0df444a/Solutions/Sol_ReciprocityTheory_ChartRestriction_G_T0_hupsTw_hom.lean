-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hupsTw_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:22:16.368023+00:00
-- url     : https://prove2.me/submissions/9e26c44a-2019-4009-ba31-6462a3e36230

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hupsTw_coeff_coeff
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R} {a : ℕ}
    (hp : ∀ s ∈ p.support, hupsWt w s = a) :
    hupsTw w p = Polynomial.C p * Polynomial.X ^ a := by
  ext j s
  rw [hupsTw_coeff_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hs : s ∈ p.support
  · rw [hp s hs]
    by_cases hj : j = a
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  · rw [MvPolynomial.mem_support_iff, not_not] at hs
    split_ifs <;> simp [hs]
end ReciprocityTheory.ChartRestriction.G.T0
