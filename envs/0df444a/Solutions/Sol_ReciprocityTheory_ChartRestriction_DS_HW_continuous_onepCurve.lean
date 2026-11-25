-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.continuous_onepCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:35.703205+00:00
-- url     : https://prove2.me/submissions/8f2f40ba-5fc6-4af0-ae39-f503ed2f40bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_mder_exp_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_toMK_onepCurve
import Theorems.Thm_UpperTheory_Reformulated_B_Qk16_isClosedEmbedding_toM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    Continuous (onepCurve ε hX) := by
  apply continuous_induced_rng.2
  apply (isClosedEmbedding_toM ε).isInducing.continuous_iff.2
  have : ((fun g : UJ ε => toM g) ∘ Subtype.val ∘ onepCurve ε hX) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
    funext t
    exact toMK_onepCurve ε hX t
  rw [this]
  exact mder_exp_cont X
end ReciprocityTheory.ChartRestriction.DS.HW
