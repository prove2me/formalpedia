-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_meas_densF__ab7e151b76c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:15.422543+00:00
-- url     : https://prove2.me/submissions/136a3b49-5950-4f01-8130-9ce5cc4dd785

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfI
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cont_cpt__b03189f8567d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_cont_dmin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_LowU_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cont_dmin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (x' : Frame X.Ψ r) :
    Measurable fun w => ENNReal.ofReal (densF X x' w) := by
  refine ENNReal.measurable_ofReal.comp ?_
  unfold densF
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  have hc : Measurable fun z : V (nd X) => ‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ 2 :=
    (((cont_dmin X τ _).comp (cont_cpt' X x')).norm.pow 2).measurable
  have e : (fun z : V (nd X) => ‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ (-2 : ℤ)) =
      fun z => (‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ 2)⁻¹ := by
    funext z; rw [zpow_neg, zpow_ofNat]
  rw [e]; exact hc.inv
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
