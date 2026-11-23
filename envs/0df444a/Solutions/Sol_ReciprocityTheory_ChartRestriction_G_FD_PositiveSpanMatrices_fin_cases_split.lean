-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.fin_cases_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:08.673185+00:00
-- url     : https://prove2.me/submissions/65706096-fde3-4561-b24f-d67a351eb38b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {n p : ℕ} (hp : p ≤ n) (c : Fin n) :
    (∃ b : Fin p, c = Fin.castLE hp b) ∨ ∃ a : Fin (n - p), c = kap hp a := by
  have hc := c.isLt
  by_cases h : (c : ℕ) < p
  · exact Or.inl ⟨⟨c, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨c - p, by omega⟩, Fin.ext ?_⟩
    show (c : ℕ) = p + (c - p)
    omega
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
