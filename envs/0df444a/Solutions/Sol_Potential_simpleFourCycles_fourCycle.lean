-- Prove2me | solution 1 for Potential.simpleFourCycles_fourCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:14.254347+00:00
-- url     : https://prove2.me/submissions/09461805-f776-4cf4-bb8d-e963ee543856

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
public import Theorems.Thm_Potential_rectangle_vertices_nodup

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (u : Payoff A) (h : SimpleFourCycleProperty u) :
    FourCycle u := by
  intro s i j hij a b
  by_cases ha : a = s i
  · rw [ha, Function.update_eq_self]
    ring
  · by_cases hb : b = s j
    · have hupdate : Function.update (Function.update s i a) j b = Function.update s i a := by
        rw [hb]
        have hj : (Function.update s i a) j = s j := by simp [Ne.symm hij]
        rw [← hj, Function.update_eq_self]
      rw [hupdate, hb, Function.update_eq_self]
      ring
    · let ms : List (Move A) := [⟨i, a⟩, ⟨j, b⟩, ⟨i, s i⟩, ⟨j, s j⟩]
      have he : endpoint s ms = s := by
        simp only [ms, endpoint_cons, endpoint_nil]
        rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self]
      have hn : (vertices s ms).dropLast.Nodup := rectangle_vertices_nodup s i j hij a b ha hb
      have hz := h s ms he hn (by rfl)
      simp only [ms, pathIntegral_cons, pathIntegral_nil] at hz
      rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self] at hz
      linarith
end Potential
