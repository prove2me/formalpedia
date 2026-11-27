-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hupsTw_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:21:37.893837+00:00
-- url     : https://prove2.me/submissions/6446690c-5927-4d5a-a258-a4785699c844

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hupsTw_coeff_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R}
    {s : σ →₀ ℕ} (hs : s ∈ p.support) : (hupsTw w p).coeff (hupsWt w s) ≠ 0 := by
  intro h
  have e := hupsTw_coeff_coeff w p (hupsWt w s) s
  rw [h, MvPolynomial.coeff_zero, if_pos rfl] at e
  exact (MvPolynomial.mem_support_iff.mp hs) e.symm
end ReciprocityTheory.ChartRestriction.G.T0
