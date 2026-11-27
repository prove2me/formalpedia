-- Prove2me | solution 1 for TreeStack.estim_le_of_stackingCandidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:35:01.086805+00:00
-- url     : https://prove2.me/submissions/be76b554-a78c-45c5-b1ae-b2247a478fbf

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
import Theorems.Thm_TreeStack_universal_stackable_mono
import Theorems.Thm_TreeStack_exists_nonstackable_mass_estim_sub_one


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    estim T ≤ t := by
  rcases ht with ⟨htTwo, hU⟩
  by_contra hNot
  have htLt : t < estim T := Nat.lt_of_not_ge hNot
  have htLe : t ≤ estim T - 1 := by omega
  have hUObs :
      UniversalStackable T.graph (estim T - 1) :=
    universal_stackable_mono T hU htTwo htLe
  rcases exists_nonstackable_mass_estim_sub_one T with
    ⟨C, hMass, hNotStackable⟩
  exact hNotStackable (hUObs C hMass)
end TreeStack
