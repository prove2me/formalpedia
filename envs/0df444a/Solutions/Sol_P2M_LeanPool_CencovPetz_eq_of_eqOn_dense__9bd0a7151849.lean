-- Prove2me | solution 1 for P2M_LeanPool_CencovPetz_eq_of_eqOn_dense__9bd0a7151849
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:22.739893+00:00
-- url     : https://prove2.me/submissions/0249fbfb-fbcb-49a9-ad8d-85cd3c3924b5

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Topology.Metrizable.Uniformity
public import Definitions.Def_LeanPool_CencovPetz_ContinuousExtension

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
namespace LeanPool.CencovPetz
theorem _root_.solution {s : Set (Simplex α)} (hs : Dense s)
    {f g : Simplex α → tangentSpace (α := α) → tangentSpace (α := α) → ℝ}
    (hf : ∀ u v, Continuous fun p : Simplex α => f p u v)
    (hg : ∀ u v, Continuous fun p : Simplex α => g p u v)
    (hfg : ∀ p ∈ s, ∀ u v, f p u v = g p u v) :
    ∀ p u v, f p u v = g p u v := by
  intro p u v
  have hEqOn :
      Set.EqOn (fun p : Simplex α => f p u v) (fun p : Simplex α => g p u v) s := by
    intro p hp
    exact hfg p hp u v
  have hfun :
      (fun p : Simplex α => f p u v) = fun p : Simplex α => g p u v :=
    Continuous.ext_on (X := ℝ) (Y := Simplex α) hs (hf u v) (hg u v) hEqOn
  exact congrArg (fun h => h p) hfun
end LeanPool.CencovPetz
