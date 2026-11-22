-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.hyperbolic_parallel_property
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:35.761123+00:00
-- url     : https://prove2.me/submissions/bf0f2d02-1c90-4cbf-9a27-fa1edb024bcc

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hyperbolic_two_parallels

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
    (∃ M₁ M₂ : Set (K × K), M₁ ≠ M₂ ∧ (IsLine (plane κ) M₁ ∧ P ∈ M₁ ∧ M₁ ∩ S = ∅) ∧
      (IsLine (plane κ) M₂ ∧ P ∈ M₂ ∧ M₂ ∩ S = ∅)) ∧
    {M : Set (K × K) | IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅}.Infinite :=
  ⟨hyperbolic_two_parallels hκ hS hP hPS, hyperbolic_parallels hκ hS hP hPS⟩
end ParallelPostulate.HyperbolicPlane
