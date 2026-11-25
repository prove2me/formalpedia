-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_mul_dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:25.510644+00:00
-- url     : https://prove2.me/submissions/8d82b91f-7214-45c8-bab4-b205c437a950

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_mul_tv

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
theorem _root_.solution (x : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a a (1 : ℂ))) r q = x r q * (if q = a then 1 + s else 1) := by
  rw [hwmf_mul_tv]
  by_cases hq : q = a
  · subst hq
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hq, if_neg hq]
    ring
end ReciprocityTheory.ChartRestriction.DS.HW
