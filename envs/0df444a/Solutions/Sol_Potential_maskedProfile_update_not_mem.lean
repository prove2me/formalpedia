-- Prove2me | solution 1 for Potential.maskedProfile_update_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:58:28.505137+00:00
-- url     : https://prove2.me/submissions/29ba2d70-0dca-42e1-91db-b882baf6632f

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
    (base s : Profile A) (S : Finset I) (j : I) (a : A j) (hj : j ∉ S) :
    maskedProfile base S (Function.update s j a) = maskedProfile base S s := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [maskedProfile, hj]
  · simp [maskedProfile, hk]
end Potential
