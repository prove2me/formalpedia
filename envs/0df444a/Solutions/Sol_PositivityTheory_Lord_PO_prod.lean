-- Prove2me | solution 1 for PositivityTheory.Lord.PO.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:25.810231+00:00
-- url     : https://prove2.me/submissions/79bb4bda-80fb-43c0-b66b-0a9b61b03083

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Theorems.Thm_PositivityTheory_Lord_PO_mul
import Theorems.Thm_PositivityTheory_Lord_PO_of_analytic

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
namespace PO
theorem _root_.solution {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (K : ι → ℕ) (h : ∀ i ∈ t, PO (F i) x (K i)) :
    PO (fun s => ∏ i ∈ t, F i s) x (∑ i ∈ t, K i) := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact PositivityTheory.Lord.PO.of_analytic analyticAt_const
  · intro a t ha ih h
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end PO
end PositivityTheory.Lord
