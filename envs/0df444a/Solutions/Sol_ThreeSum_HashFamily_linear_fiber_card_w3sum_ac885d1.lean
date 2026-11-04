-- Prove2me | solution 1 for ThreeSum.HashFamily.linear_fiber_card_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:33.569338+00:00
-- url     : https://prove2.me/submissions/a4319945-2afa-43f4-811a-6586b5064ee5

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]
namespace ThreeSum.HashFamily
theorem _root_.solution {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W] [DecidableEq W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (target : W) :
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
      Fintype.card V := by
  classical
  have heq : ∀ y : W, (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = target)).card := by
    intro y
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf target)
  calc
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
        ∑ y : W, (Finset.univ.filter (fun x => f x = y)).card := by
      simp [heq]
    _ = ∑ y : W, ∑ x : V, if f x = y then (1 : ℕ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x : V, ∑ y : W, if f x = y then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by simp
end ThreeSum.HashFamily
