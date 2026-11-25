-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_pnorm_sub_le__9a0fedfcc007
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:15.59904+00:00
-- url     : https://prove2.me/submissions/41801399-0fb1-4996-8a48-a8b2be6f9bf5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStartPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_pnorm_eq__d17dff18dae0
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_nonneg__30ef8672819a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
theorem _root_.solution (la : Wt X.Ψ r) (f g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (fun y => f y - g y) x ≤ X.pnorm la f x + X.pnorm la g x := by
  rw [pnorm_eq', pnorm_eq', pnorm_eq', ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (nfac_nonneg' X la x)
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
