-- Prove2me | solution 1 for Potential.endpoint_setMoves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:00:45.4688+00:00
-- url     : https://prove2.me/submissions/8df9aa76-372b-4b27-b5af-2af77e1aa168

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

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (base target : Profile A) (is : List I) (j : I) :
    endpoint base (is.map (fun i => (⟨i, target i⟩ : Move A))) j =
      if j ∈ is then target j else base j := by
  induction is generalizing base with
  | nil => simp [endpoint_nil]
  | cons i is ih =>
    simp only [List.map_cons, endpoint_cons, ih, List.mem_cons]
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
end Potential
