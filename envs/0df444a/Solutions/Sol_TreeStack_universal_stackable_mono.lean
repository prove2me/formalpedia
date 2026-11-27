-- Prove2me | solution 1 for TreeStack.universal_stackable_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:42.214836+00:00
-- url     : https://prove2.me/submissions/cc870626-036e-47d1-8f64-71a44ff7d8cc

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
import Theorems.Thm_TreeStack_universal_stackable_succ


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V]
    (T : FiniteTree V) {s t : ℕ}
    (hU : UniversalStackable T.graph s)
    (hs : 2 ≤ s) (hst : s ≤ t) :
    UniversalStackable T.graph t := by
  induction t, hst using Nat.le_induction with
  | base =>
      exact hU
  | succ t hst ih =>
      exact
        universal_stackable_succ
          T.isTree.connected ih (by omega)
end TreeStack
