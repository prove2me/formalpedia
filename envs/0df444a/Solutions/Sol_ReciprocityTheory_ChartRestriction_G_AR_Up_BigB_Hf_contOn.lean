-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.BigB.Hf_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:29.973283+00:00
-- url     : https://prove2.me/submissions/aea10df4-fd34-4e5d-bb6c-00af94bc9eb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModelNefness
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BigStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_BigB_w_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_BigB_S_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_BigB_pnorm_contOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.BigB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.BigB
theorem _root_.solution (X : Data E r) (Xa : ArchInM X) : ContinuousOn (Hf X Xa) X.dom := by
  have hw : ∀ k, ContinuousOn (X.pnorm Xa.L (Xa.w k)) X.dom :=
    fun k => pnorm_contOn X Xa.L (w_sec X Xa k)
  have he : ContinuousOn (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et) X.dom :=
    pnorm_contOn X _ Xa.et_sec
  unfold Hf
  apply ContinuousOn.div
  · apply ContinuousOn.rpow_const (he.pow 2)
    intro x _
    right
    positivity
  · exact (continuousOn_finset_sum _ fun k _ => (hw k).pow 2).pow 2
  · intro x hx
    exact pow_ne_zero _ (S_pos X Xa hx).ne'
end ReciprocityTheory.ChartRestriction.G.AR.Up.BigB
