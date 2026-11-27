-- Prove2me | solution 1 for PositivityTheory.Lord.meromorphicAt_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:44.328336+00:00
-- url     : https://prove2.me/submissions/17149651-b345-4283-849d-8b0e5fed83c0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd

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
theorem _root_.solution {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (h : ∀ i ∈ t, MeromorphicAt (F i) x) :
    MeromorphicAt (fun s => ∏ i ∈ t, F i s) x := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact MeromorphicAt.const 1 x
  · intro a t ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a t)).fun_mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end PositivityTheory.Lord
