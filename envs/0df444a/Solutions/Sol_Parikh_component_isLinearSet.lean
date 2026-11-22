-- Prove2me | solution 1 for Parikh.component_isLinearSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:35.227267+00:00
-- url     : https://prove2.me/submissions/6ed4753c-e10d-4c85-a4c0-31c29daa6a22

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting
public import Theorems.Thm_Parikh_Component_denotation_eq_vadd_closure

set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} (c : Component T) :
    IsLinearSet c.denotation := by
  exact ⟨c.base, Set.range c.periods.get, Set.finite_range _,
    c.denotation_eq_vadd_closure⟩
end Parikh
