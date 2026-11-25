-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.nF_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:01.92801+00:00
-- url     : https://prove2.me/submissions/7432bb18-9534-47c8-a48e-e50d85160a62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_diffOn_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (τ : X.Ψ) (a c : Fin r) : DifferentiableOn ℂ (fun x => nF X x0 x τ a c) (cellL X x0) :=
  diffOn_inv (fun x => Lm (Mx X x0 x τ)) (fun i k => Lm_diff τ i k)
    (fun x _ => by rw [Lm_det]; exact one_ne_zero) a c
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
