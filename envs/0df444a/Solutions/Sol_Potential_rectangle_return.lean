-- Prove2me | solution 1 for Potential.rectangle_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:52:23.198658+00:00
-- url     : https://prove2.me/submissions/5feb0ee0-930c-4243-bcfc-6ed61c619cf1

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
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (s : Profile A) (i j : I) (hij : i ≠ j)
    (a : A i) (b : A j) :
    Function.update (Function.update (Function.update s i a) j b) i (s i) =
      Function.update s j b := by
  rw [Function.update_comm (Ne.symm hij), Function.update_idem, Function.update_eq_self]
end Potential
