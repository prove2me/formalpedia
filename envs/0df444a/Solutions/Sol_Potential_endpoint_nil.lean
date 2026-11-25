-- Prove2me | solution 1 for Potential.endpoint_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:52:03.769839+00:00
-- url     : https://prove2.me/submissions/355518f9-bd58-47be-99c7-c133b10b3251

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

set_option autoImplicit true
@[expose] public section
public section
open Potential
namespace Potential
theorem _root_.solution {I : Type*} {A : I → Type*} [DecidableEq I]
    (s : Profile A) : endpoint s [] = s := by
  simp only [endpoint, List.foldl_nil]
end Potential
