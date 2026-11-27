-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hupsTw_coeff_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:13:41.950437+00:00
-- url     : https://prove2.me/submissions/9f22283d-993f-4da8-9175-c64e742dcec4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hupsTw_eq
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
theorem _root_.solution {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R)
    (j : ℕ) (s : σ →₀ ℕ) :
    ((hupsTw w p).coeff j).coeff s = if hupsWt w s = j then p.coeff s else 0 := by
  classical
  rw [hupsTw_eq, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (MvPolynomial.coeff s), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  rw [Finset.sum_eq_single s]
  · by_cases h : hupsWt w s = j
    · rw [if_pos h.symm, if_pos h, if_pos rfl]
    · simp [h, Ne.symm h]
  · intro t _ hts
    simp [hts, MvPolynomial.coeff_monomial]
  · intro hs
    rw [MvPolynomial.mem_support_iff, not_not] at hs
    simp [hs]
end ReciprocityTheory.ChartRestriction.G.T0
