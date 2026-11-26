-- Prove2me | solution 1 for TreeStack.rootEstimate_corrected_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:09.538992+00:00
-- url     : https://prove2.me/submissions/367a8a61-541d-4dea-af02-3b3677dd5aad

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_sigma_corrected_expansion

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + leafCount T r + T.graph.degree r +
        ∑ v ∈ nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by
  rw [rootEstimate, sigma_corrected_expansion]
  omega
end TreeStack
