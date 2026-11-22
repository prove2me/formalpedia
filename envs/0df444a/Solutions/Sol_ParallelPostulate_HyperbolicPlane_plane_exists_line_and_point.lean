-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_exists_line_and_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:08:34.493331+00:00
-- url     : https://prove2.me/submissions/1ca21665-4f26-4e30-89fc-7a449aa59523

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_exists_line_and_point
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_zero_mem_plane
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_openAlong

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : K) :
    ∃ (S : Set (K × K)) (P : K × K), IsLine (plane κ) S ∧ P ∈ plane κ ∧ P ∉ S :=
  exists_line_and_point (plane_openAlong κ) (zero_mem_plane κ)
end ParallelPostulate.HyperbolicPlane
