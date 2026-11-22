-- Prove2me | solution 1 for Parikh.isRegular_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:25.576582+00:00
-- url     : https://prove2.me/submissions/340f95d3-2603-4db0-8b4a-55ebc93e5ef7

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
theorem _root_.solution : (1 : Language T).IsRegular := by
  apply isRegular_of_finite_language_cover _ {1} (Set.finite_singleton _) (by simp)
  intro K hK a w hw
  have hK : K = 1 := Set.mem_singleton_iff.mp hK
  subst K
  simp only [Language.mem_one, List.cons_ne_nil] at hw
end Parikh
