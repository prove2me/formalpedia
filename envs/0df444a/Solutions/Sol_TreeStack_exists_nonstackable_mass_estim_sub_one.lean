-- Prove2me | solution 1 for TreeStack.exists_nonstackable_mass_estim_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:40.398597+00:00
-- url     : https://prove2.me/submissions/8468268d-b16e-431b-87c7-18390d20865d

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_mass_obstruction
import Theorems.Thm_TreeStack_obstruction_not_stackable
import Theorems.Thm_TreeStack_exists_rootEstimate_eq_estim

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V] (T : FiniteTree V) :
    ∃ C : Configuration V,
      mass C = estim T - 1 ∧
        ¬ Stackable T.graph C := by
  classical
  rcases exists_rootEstimate_eq_estim T with ⟨r, hr⟩
  refine ⟨obstruction T r, ?_, obstruction_not_stackable T r⟩
  rw [mass_obstruction T r, hr]
end TreeStack
