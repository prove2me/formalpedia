-- Prove2me | solution 1 for Potential.endpoint_all_setMoves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:04:04.298491+00:00
-- url     : https://prove2.me/submissions/89ac5fb2-8af7-44e3-ab1e-5b2507511ddf

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
public import Theorems.Thm_Potential_endpoint_setMoves

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution [Fintype I] (base target : Profile A) :
    endpoint base (Finset.univ.toList.map (fun i => (⟨i, target i⟩ : Move A))) = target := by
  funext j
  simp [endpoint_setMoves]
end Potential
