-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_mul_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:35:49.875222+00:00
-- url     : https://prove2.me/submissions/74b2fe1a-fb69-4b6c-84e1-3fa19671852b

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
theorem _root_.solution (x : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a b (1 : ℂ))) r q = x r q + (if q = b then s * x r a else 0) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  congr 1
  by_cases hq : q = b
  · subst hq
    rw [if_pos rfl, Matrix.mul_apply]
    simp [Matrix.single_apply]
  · rw [if_neg hq, Matrix.mul_apply]
    simp [Matrix.single_apply, Ne.symm hq]
end ReciprocityTheory.ChartRestriction.DS.HW
