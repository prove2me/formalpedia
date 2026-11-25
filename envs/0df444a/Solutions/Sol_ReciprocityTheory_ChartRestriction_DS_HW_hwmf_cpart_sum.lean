-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_cpart_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:47.183313+00:00
-- url     : https://prove2.me/submissions/d65836bf-9eb5-4020-a6b4-4af15999af83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun

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
theorem _root_.solution (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  ext i j
  first
    | (simp
       linear_combination (-(1 / 2) * (Z i j + (Jm ε * Zᴴ * Jm ε) i j)) * Complex.I_sq)
    | (simp [Complex.I_sq]; ring)
end ReciprocityTheory.ChartRestriction.DS.HW
