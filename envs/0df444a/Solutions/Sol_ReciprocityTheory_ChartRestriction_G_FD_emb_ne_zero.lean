-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:04.372334+00:00
-- url     : https://prove2.me/submissions/0531445c-86ac-4370-93cc-54a4ff78f75b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    {u : Fin r → E} (hu : u ≠ 0) : Data.emb τ u ≠ 0 := by
  intro h
  apply hu
  funext a
  have h1 := congrFun h a
  simp only [Data.emb, Pi.zero_apply] at h1
  exact (map_eq_zero τ).1 h1
end ReciprocityTheory.ChartRestriction.G.FD
