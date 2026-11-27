-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.continuous_f0K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:10.504646+00:00
-- url     : https://prove2.me/submissions/f72b3e07-ef6b-4a26-8b55-86ab56352e4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_differentiable_highest_weight_fn

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (f0K ε m) := by
  have hc : Continuous (toMK (ε := ε)) := by
    first
      | exact continuous_toMK
      | exact continuous_toMK ε
      | (unfold toMK; fun_prop)
      | (unfold toMK; exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  exact (differentiable_highest_weight_fn ε m).continuous.comp hc
end ReciprocityTheory.ChartRestriction.DS.HW
