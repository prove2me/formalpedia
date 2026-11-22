-- Prove2me | solution 1 for Parikh.isRegular_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:21.041597+00:00
-- url     : https://prove2.me/submissions/9601b1ea-612e-4588-9f4f-c5e121a9b8c9

module
public import Mathlib.Computability.DFA
public import Mathlib.Computability.NFA
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Theorems.Thm_Parikh_isRegular_of_finite_language_cover

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution : (0 : Language T).IsRegular := by
  apply isRegular_of_finite_language_cover _ {0} (Set.finite_singleton _) (by simp)
  intro K hK a w hw
  have hK : K = 0 := Set.mem_singleton_iff.mp hK
  subst K
  exact (Language.notMem_zero _ hw).elim
end Parikh
