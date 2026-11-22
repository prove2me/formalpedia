-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.hyperbolic_two_parallels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:10:32.738443+00:00
-- url     : https://prove2.me/submissions/9a7c3371-a617-43d4-a9e3-91defde3b285

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hyperbolic_parallels

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} (hκ : κ < 0) {S : Set (K × K)}
    (hS : IsLine (plane κ) S) {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    ∃ M₁ M₂ : Set (K × K), M₁ ≠ M₂ ∧ (IsLine (plane κ) M₁ ∧ P ∈ M₁ ∧ M₁ ∩ S = ∅) ∧
      (IsLine (plane κ) M₂ ∧ P ∈ M₂ ∧ M₂ ∩ S = ∅) := by
  obtain ⟨M₁, h₁, M₂, h₂, hne⟩ := (hyperbolic_parallels hκ hS hP hPS).nontrivial
  exact ⟨M₁, M₂, hne, h₁, h₂⟩
end ParallelPostulate.HyperbolicPlane
