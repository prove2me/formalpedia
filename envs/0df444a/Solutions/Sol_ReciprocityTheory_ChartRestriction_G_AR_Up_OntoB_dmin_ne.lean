-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.dmin_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:09.08812+00:00
-- url     : https://prove2.me/submissions/5a2ba53e-236b-44db-b5f0-ffa951527de6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open scoped ComplexConjugate ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
variable {X x0}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
theorem _root_.solution {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
  intro h0
  have h1 : 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := (hz τ).2 i
  rw [h0, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
