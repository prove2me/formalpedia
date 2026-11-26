-- Prove2me | solution 1 for TreeStack.rootEstimate_le_estim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:44.348365+00:00
-- url     : https://prove2.me/submissions/69aef379-71aa-46df-a5b4-6c29e8e0c682

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r ≤ estim T := by
  simpa [estim] using
    (Finset.le_sup (f := rootEstimate T) (Finset.mem_univ r))
end TreeStack
