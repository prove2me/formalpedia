-- Prove2me | solution 1 for Potential.remove_noop_moves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:59:03.229638+00:00
-- url     : https://prove2.me/submissions/a91ae1ec-c986-4f7e-b9a3-cd7ce9aec8c8

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
public import Theorems.Thm_Potential_endpoint_cons
public import Theorems.Thm_Potential_pathIntegral_cons

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (u : Payoff A) (s : Profile A) (ms : List (Move A)) :
    ∃ ns : List (Move A), ActualPath s ns ∧ endpoint s ns = endpoint s ms ∧
      pathIntegral u s ns = pathIntegral u s ms := by
  classical
  induction ms generalizing s with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | cons m ms ih =>
    by_cases hm : m.2 = s m.1
    · have hu : Function.update s m.1 m.2 = s := by
        rw [hm, Function.update_eq_self]
      obtain ⟨ns, hn, he, hv⟩ := ih s
      refine ⟨ns, hn, ?_, ?_⟩
      · simpa only [endpoint_cons, hu] using he
      · simpa only [pathIntegral_cons, hu, sub_self, zero_add] using hv
    · obtain ⟨ns, hn, he, hv⟩ := ih (Function.update s m.1 m.2)
      refine ⟨m :: ns, ⟨hm, hn⟩, ?_, ?_⟩
      · simpa only [endpoint_cons] using he
      · simpa only [pathIntegral_cons] using congrArg
          (fun z => u m.1 (Function.update s m.1 m.2) - u m.1 s + z) hv
end Potential
