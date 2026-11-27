-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.BigA.projPerp_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:16.152845+00:00
-- url     : https://prove2.me/submissions/fb94e43b-fc95-43f9-a1dc-f385f0f6d665

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BigStatementPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sqNorm_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.BigA
open Complex Matrix ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.BigA
theorem _root_.solution {N : ℕ} (g0 : Fin N → ℂ) (h : g0 ≠ 0) : projPerp g0 *ᵥ g0 = 0 := by
  have hs : (sqNorm g0 : ℂ) ≠ 0 := by
    exact_mod_cast (sqNorm_pos h).ne'
  have e : star g0 ⬝ᵥ g0 = (sqNorm g0 : ℂ) := by
    simp [sqNorm, dotProduct, Complex.normSq_eq_conj_mul_self]
  funext i
  simp only [projPerp, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  rw [show (vecMulVec g0 (star g0) *ᵥ g0) i = g0 i * (star g0 ⬝ᵥ g0) by
    simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_assoc], e]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.BigA
