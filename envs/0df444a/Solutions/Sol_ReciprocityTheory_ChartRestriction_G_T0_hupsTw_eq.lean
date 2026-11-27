-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hupsTw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:55:54.590849+00:00
-- url     : https://prove2.me/submissions/d62788b5-09d6-4eff-87ef-6a33f5a9680d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hupsTw_monomial
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
theorem _root_.solution {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R) :
    hupsTw w p = ∑ s ∈ p.support,
      Polynomial.C (MvPolynomial.monomial s (p.coeff s)) * Polynomial.X ^ hupsWt w s := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [hupsTw_monomial]
end ReciprocityTheory.ChartRestriction.G.T0
