-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:46.767796+00:00
-- url     : https://prove2.me/submissions/e9bbdb87-a3c2-461b-b41e-235f1bc59c4d

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
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = (gramF τ.1 X.Gm (famN (mat x τ) i (Nat.le_of_lt_succ i.isLt))).det := rfl
end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
