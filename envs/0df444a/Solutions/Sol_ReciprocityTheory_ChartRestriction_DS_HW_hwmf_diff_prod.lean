-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_diff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:57:02.818986+00:00
-- url     : https://prove2.me/submissions/da958665-6a26-444c-9da6-de25909fadbc

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
theorem _root_.solution {ι : Type} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i, Differentiable ℂ (g i)) : Differentiable ℂ (fun x => ∏ i ∈ s, g i x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiable_const _
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih
end ReciprocityTheory.ChartRestriction.DS.HW
