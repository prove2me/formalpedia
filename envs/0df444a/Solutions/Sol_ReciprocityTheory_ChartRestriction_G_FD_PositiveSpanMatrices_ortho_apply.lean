-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:21.798988+00:00
-- url     : https://prove2.me/submissions/f8d6157e-27da-4bb0-b330-9eff30551922

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (c d : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) c) (col (mat x τ) d) = if c = d then ((sgn X.p0 c : ℝ) : ℂ) else 0 := by
  have h := congrFun (congrFun (hx τ) c) d
  simpa [gram, Matrix.diagonal_apply] using h
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
