-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.log_densF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:49.694929+00:00
-- url     : https://prove2.me/submissions/5809c468-70f5-426a-9d34-5b2e06b870ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
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
theorem _root_.solution {z : V (nd X)} (hz : z ∈ OmF X x0) : Real.log (densF X x0 z) = LD X x0 z := by
  have hp : ∀ (τ : X.Ψ) (i : Fin r), 0 < ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^ (-2 : ℤ) :=
    fun τ i => zpow_pos (norm_pos_iff.mpr (dmin_ne hz τ i.castSucc)) _
  unfold densF LD
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => hp τ i).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (hp τ i).ne')]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_zpow]
  norm_num
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
