-- Prove2me | solution 1 for Potential.endpoint_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:52:10.465593+00:00
-- url     : https://prove2.me/submissions/a663dc4c-f4c1-42c8-af9c-f2ce50e061ba

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
    (s : Profile A) (m : Move A) (ms : List (Move A)) :
    endpoint s (m :: ms) = endpoint (Function.update s m.1 m.2) ms := by
  simp only [endpoint, List.foldl_cons]
end Potential
