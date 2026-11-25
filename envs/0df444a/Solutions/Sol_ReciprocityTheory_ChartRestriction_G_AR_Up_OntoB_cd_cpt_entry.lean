-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.cd_cpt_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:04.300134+00:00
-- url     : https://prove2.me/submissions/af90f983-ca5c-4ef0-b663-535af3b36c08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_cd_nmat

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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
theorem _root_.solution (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => cpt X x0 z τ a b := by
  have he : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ c, x0 τ a c * nmat X z τ c b := by
    funext z
    simp [cpt, rmul, mat, Matrix.mul_apply]
  rw [he]
  exact ContDiff.sum fun c _ => contDiff_const.mul (cd_nmat X τ c b)
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
