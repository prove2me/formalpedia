-- Prove2me | solution 1 for Potential.maskedProfile_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:58:30.592245+00:00
-- url     : https://prove2.me/submissions/950f8694-267a-407e-9c06-4c9776bc4f12

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
    (base s : Profile A) (S : Finset I) (i : I) :
    maskedProfile base (insert i S) s =
      Function.update (maskedProfile base S s) i (s i) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [maskedProfile]
  · simp [maskedProfile, hk]
end Potential
