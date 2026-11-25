-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.finrank_maxUnramifiedSubfield_padicFinExt_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:36.979224+00:00
-- url     : https://prove2.me/submissions/8f8d385c-19f9-416d-9783-8995229a6fb3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_one_le_normSq_jacU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_measurable_normSq_jacU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_ball_subset_Cy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : 0 < K0 ι r := by
  unfold K0
  calc (0 : ENNReal)
      < volume (Metric.ball (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) (1 / 2)) :=
        Metric.measure_ball_pos _ _ (by norm_num)
    _ ≤ volume (Cy ι r) := measure_mono ball_subset_Cy
    _ = ∫⁻ _y in Cy ι r, 1 := (setLIntegral_one _).symm
    _ ≤ ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y)) :=
        setLIntegral_mono measurable_normSq_jacU fun y hy => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_normSq_jacU hy)
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
