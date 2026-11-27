-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hupsTw_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:36:13.185032+00:00
-- url     : https://prove2.me/submissions/ebb11118-ea0e-4da6-8901-26fec16054d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
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
theorem _root_.solution {σ R : Type*} [CommRing R] (w : σ → ℕ) (s : σ →₀ ℕ) (a : R) :
    hupsTw w (MvPolynomial.monomial s a) =
      Polynomial.C (MvPolynomial.monomial s a) * Polynomial.X ^ hupsWt w s := by
  rw [hupsTw, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, hupsWt, Finsupp.prod, Finsupp.sum, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  simp only [mul_comm (w _) _]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring
end ReciprocityTheory.ChartRestriction.G.T0
