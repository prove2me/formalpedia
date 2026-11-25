-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_hasDerivAt_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:53.614966+00:00
-- url     : https://prove2.me/submissions/863e81a5-26c9-4780-a136-e060df498f8e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_hasDerivAt_exp_entry


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
theorem _root_.solution (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => Y * NormedSpace.exp ((t : ℂ) • X)) (Y * X) 0 := by
  refine hasDerivAt_pi.2 fun i => ?_
  refine hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  refine HasDerivAt.fun_sum fun k _ => HasDerivAt.const_mul _ ?_
  have h := InhabA.hasDerivAt_exp_entry X k j
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) k j) = fun t : ℝ => (NormedSpace.exp (t • X)) k j := by
    funext t; congr 3
  rw [e]; exact h
end ReciprocityTheory.ChartRestriction.DS.HW
