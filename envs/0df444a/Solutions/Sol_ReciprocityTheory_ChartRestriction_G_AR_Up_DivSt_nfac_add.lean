-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt.nfac_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:05:57.890813+00:00
-- url     : https://prove2.me/submissions/baf44a03-8ea3-499e-abb4-2c0525eebdac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStartPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_ne_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    X.nfac (la + la') x = X.nfac la x * X.nfac la' x := by
  unfold Data.nfac
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hpos : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    norm_pos_iff.mpr (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))
  rw [← Real.rpow_add hpos]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
