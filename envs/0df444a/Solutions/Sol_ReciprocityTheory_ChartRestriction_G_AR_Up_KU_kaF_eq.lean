-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.kaF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:00.272925+00:00
-- url     : https://prove2.me/submissions/ab7f633f-6c21-470f-bd8f-433dc714311c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_Yb_tl_nM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_Mx_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_det_one_sub_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_norm_of_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) : kaF X x0 bb z = kap X x0 bb (cpt X x0 z) := by
  have hpos : ∀ τ, 0 < (ExF.Am X z τ).det := fun τ => ((ExF.mem_OmF_iff X x0 ho z).1 hz τ).det_pos
  have hfac : ∀ τ, dpow (Yb (Mx X x0 (cpt X x0 z) τ)) bb = ‖(ExF.Am X z τ).det‖ ^ bb := by
    intro τ
    rw [Mx_cpt X ho, Yb_tl_nM, dpow, det_one_sub_tr, ExF.norm_of_pos (hpos τ)]; rfl
  rw [kap, Finset.prod_congr rfl (fun τ _ => hfac τ), kaF, ExF.rhF_eq_sum X x0 ho z]
  calc Real.exp (-bb * -∑ τ, Real.log ‖(ExF.Am X z τ).det‖)
      = ∏ τ, Real.exp (Real.log ‖(ExF.Am X z τ).det‖ * bb) := by
        rw [← Real.exp_sum]; congr 1; rw [neg_mul_neg, Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    _ = ∏ τ, ‖(ExF.Am X z τ).det‖ ^ bb :=
        Finset.prod_congr rfl fun τ _ => (Real.rpow_def_of_pos (norm_pos_iff.2 (hpos τ).ne') bb).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
