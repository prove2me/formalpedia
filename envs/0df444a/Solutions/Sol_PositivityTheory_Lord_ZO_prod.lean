-- Prove2me | solution 1 for PositivityTheory.Lord.ZO.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:31.677967+00:00
-- url     : https://prove2.me/submissions/9ed615ab-d433-4d99-966d-62ec224b0e20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Theorems.Thm_PositivityTheory_Lord_PO_mul
import Theorems.Thm_PositivityTheory_Lord_PO_of_analytic
import Theorems.Thm_PositivityTheory_Lord_ZO_mul
import Theorems.Thm_PositivityTheory_Lord_ZO_of_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open PositivityTheory PositivityTheory.Lord
variable {f g : ℂ → ℂ} {x : ℂ} {k l m n : ℕ}
namespace PositivityTheory.Lord
namespace ZO
theorem _root_.solution {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (K : ι → ℕ) (h : ∀ i ∈ t, ZO (F i) x (K i)) :
    ZO (fun s => ∏ i ∈ t, F i s) x (∑ i ∈ t, K i) := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact PositivityTheory.Lord.ZO.of_analytic analyticAt_const one_ne_zero
  · intro a t ha ih h
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end ZO
end PositivityTheory.Lord
