-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfa_cm_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:38.084655+00:00
-- url     : https://prove2.me/submissions/6052f78f-6843-42c9-b29e-7714e47a5502

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (x : Fin n × Fin n) (l : List (Fin n × Fin n)) (hx : x ∉ l) :
    cmFock x.1 x.2 (l.map fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod = 0 := by
  induction l with
  | nil => simp [cmFock]
  | cons y l ih =>
    rw [List.mem_cons, not_or] at hx
    have ih' := ih hx.2
    simp only [cmFock] at ih' ⊢
    rw [List.map_cons, List.prod_cons, CliffordAlgebra.contractLeft_ι_mul, ih']
    simp [hx.1]
end ReciprocityTheory.ChartRestriction.DS
