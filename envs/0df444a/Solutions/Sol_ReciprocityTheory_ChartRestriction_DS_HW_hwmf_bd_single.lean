-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_bd_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:59:00.480036+00:00
-- url     : https://prove2.me/submissions/151473c8-639a-495e-9353-c1749cb2c91b

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
theorem _root_.solution (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) :
    bdPart ε (single a b (1 : ℂ)) = single a b 1 := by
  ext i j
  simp only [bdPart, Matrix.of_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos he]
  · rw [Matrix.single_apply, if_neg h, ite_self]
end ReciprocityTheory.ChartRestriction.DS.HW
