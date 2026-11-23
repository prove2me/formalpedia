-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.perp_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:56.625102+00:00
-- url     : https://prove2.me/submissions/55042a79-2f17-493b-a218-478bc89b2828

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
theorem _root_.solution {s : Set (Fin r → ℂ)} {v : Fin r → ℂ} (h : ∀ y ∈ s, hermC τ G y v = 0) :
    ∀ y ∈ Submodule.span ℂ s, hermC τ G y v = 0 := by
  intro y hy
  have hle : Submodule.span ℂ s ≤ LinearMap.ker (hL τ G v) :=
    Submodule.span_le.mpr (fun z hz => LinearMap.mem_ker.mpr (h z hz))
  exact LinearMap.mem_ker.mp (hle hy)
end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
