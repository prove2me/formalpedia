-- Prove2me | solution 1 for Potential.closedPaths_fourCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:58:56.284278+00:00
-- url     : https://prove2.me/submissions/a2db98ac-5622-417d-ad96-9cc934be2dd3

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
public import Theorems.Thm_Potential_endpoint_nil
public import Theorems.Thm_Potential_endpoint_cons
public import Theorems.Thm_Potential_pathIntegral_nil
public import Theorems.Thm_Potential_pathIntegral_cons
public import Theorems.Thm_Potential_rectangle_return

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (u : Payoff A) (h : ClosedPathProperty u) : FourCycle u := by
  intro s i j hij a b
  let ms : List (Move A) := [⟨i, a⟩, ⟨j, b⟩, ⟨i, s i⟩, ⟨j, s j⟩]
  have he : endpoint s ms = s := by
    simp only [ms, endpoint_cons, endpoint_nil]
    rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self]
  have hz := h s ms he
  simp only [ms, pathIntegral_cons, pathIntegral_nil] at hz
  rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self] at hz
  linarith
end Potential
