-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:52.802352+00:00
-- url     : https://prove2.me/submissions/63510262-2875-4c78-abc8-02e3ee7d6594

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
theorem _root_.solution (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) : mN τ G x e 0 = 0 := by
  simp [mN, pN, pv, hermC]
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
