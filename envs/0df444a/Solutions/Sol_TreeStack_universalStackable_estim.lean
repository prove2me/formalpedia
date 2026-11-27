-- Prove2me | solution 1 for TreeStack.universalStackable_estim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:48:56.259595+00:00
-- url     : https://prove2.me/submissions/dc9a4eca-adb8-4344-8349-9067ca500594

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
import Theorems.Thm_TreeStack_nonstackable_mass_le_estim_sub_one
import Theorems.Thm_TreeStack_card_add_one_le_estim


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V]
    (T : FiniteTree V) :
    UniversalStackable T.graph (estim T) := by
  intro C hMass
  by_contra hNot
  have hUpper :=
    nonstackable_mass_le_estim_sub_one T C hNot
  rw [hMass] at hUpper
  have hEstimPos := card_add_one_le_estim T
  omega
end TreeStack
