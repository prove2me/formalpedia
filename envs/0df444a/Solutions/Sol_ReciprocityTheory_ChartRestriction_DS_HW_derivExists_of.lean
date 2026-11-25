-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.derivExists_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:53.554971+00:00
-- url     : https://prove2.me/submissions/8b881369-b425-425f-82ac-5dddfee19a60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_derivExists_of_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blk_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_continuous_blkEmbed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_blkRes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_toMK_onepCurve


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (h : DerivExistsAllPosStatement) : DerivExistsStatement := by
  intro n ε V _ _ _ τ hτ
  refine derivExists_of_split h ε (blkP ε) (blkEmbed ε) (continuous_blkEmbed ε) (blkRes ε)
    (fun s X hX => inK_blkRes hX s) (fun X hX t => ?_) V τ hτ
  have hc := blk_curve hX (onepCurve ε hX) (toMK_onepCurve ε hX)
    (onepCurve _ (inK_blkRes hX true)) (toMK_onepCurve _ (inK_blkRes hX true))
    (onepCurve _ (inK_blkRes hX false)) (toMK_onepCurve _ (inK_blkRes hX false)) t
  have h1 := congrArg toMK hc
  rw [toMK_onepCurve] at h1
  exact h1.symm
end ReciprocityTheory.ChartRestriction.DS.HW
