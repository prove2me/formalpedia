-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.LD_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:11:26.751928+00:00
-- url     : https://prove2.me/submissions/9c41ca49-2395-4f7f-813b-06f1fa2f32d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_cd_dmin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_dmin_ne

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
variable (X x0)
variable {X x0}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
theorem _root_.solution {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (LD X x0) z := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ContDiffAt ℝ ∞ (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hne := dmin_ne hz τ i
    have h1 : ContDiffAt ℝ ∞ (fun w => ‖dmin X.Gm (cpt X x0 w) τ i‖) z :=
      (contDiffAt_norm ℂ hne).comp z (cd_dmin X x0 τ i).contDiffAt
    exact h1.log (norm_ne_zero_iff.mpr hne)
  unfold LD
  exact ContDiffAt.sum fun τ _ => ContDiffAt.sum fun i _ => contDiffAt_const.mul (hd τ i.castSucc)
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
