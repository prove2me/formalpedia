-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_invF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:18.316743+00:00
-- url     : https://prove2.me/submissions/5eef5219-722c-4dbc-830e-d764524d2ee3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
private lemma mem_bor_iff' {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} :
    b ∈ Bor Ψ r ↔ ∀ τ : Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 :=
  Iff.rfl
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rmul b (invF X b) = oneF X := by
  funext τ
  show mat b τ * (mat b τ)⁻¹ = (1 : Matrix (Fin r) (Fin r) ℂ)
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (mem_bor_iff'.1 hb τ).1)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
