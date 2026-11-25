-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowComp_tensAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:20.451385+00:00
-- url     : https://prove2.me/submissions/595beea8-e5a3-4cfc-b8cc-3a61b4a6a4d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_LowComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] {n : ℕ} (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A M a b x i = A a b (x i) + ∑ j, M a b i j • x j := by
  simp [tensAct]
end ReciprocityTheory.ChartRestriction.DS.HW
