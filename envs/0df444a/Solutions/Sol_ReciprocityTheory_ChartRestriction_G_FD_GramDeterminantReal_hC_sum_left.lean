-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:58.636388+00:00
-- url     : https://prove2.me/submissions/09e7ac8f-26b1-4a83-906f-9ad2da71f683

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution {n : ℕ} (f : Fin n → Fin r → ℂ) (w : Fin n → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, w b • f b) v = ∑ b, w b * hermC τ G (f b) v := by
  change (hL τ G v) (∑ b, w b • f b) = ∑ b, w b * (hL τ G v) (f b)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
