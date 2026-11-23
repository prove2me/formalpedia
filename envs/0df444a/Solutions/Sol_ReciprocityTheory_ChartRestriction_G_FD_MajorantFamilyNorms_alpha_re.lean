-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.alpha_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:46.346402+00:00
-- url     : https://prove2.me/submissions/37ab389c-13e1-43bc-ab86-c8705f4351bd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantFamilyNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
theorem _root_.solution (c : ℝ) (s : ℂ) : (-I * (c : ℂ) * s) + conj (-I * (c : ℂ) * s) =
    ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring
end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
