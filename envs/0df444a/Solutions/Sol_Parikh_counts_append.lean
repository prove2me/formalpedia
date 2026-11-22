-- Prove2me | solution 1 for Parikh.counts_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:47:59.547007+00:00
-- url     : https://prove2.me/submissions/cd22ec21-7ae3-4074-ab0d-6b63d909d0ab

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting

set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [DecidableEq T] (u v : List T) :
    counts (u ++ v) = counts u + counts v := by
  funext a
  exact List.count_append
end Parikh
