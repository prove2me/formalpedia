-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.miss_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:08:12.679658+00:00
-- url     : https://prove2.me/submissions/a4f52152-16fb-4929-8949-6acda1617be7

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_common_of_cross_ne_zero
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_points_eq_of_two_common
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_no_common_of_cross_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (Pl : Set (K × K)) (L M : Dim K) (hL : L.zero ≠ L.one) {P : K × K}
    (hP : P ∈ M.points) (hPL : P ∉ L.points) :
    (M.points ∩ Pl) ∩ (L.points ∩ Pl) = ∅ ↔
      cross L.dir M.dir = 0 ∨ ∃ Q, Q ∈ L.points ∧ Q ∈ M.points ∧ Q ∉ Pl := by
  constructor
  · intro h
    by_cases hc : cross L.dir M.dir = 0
    · exact Or.inl hc
    · right
      obtain ⟨Q, hQL, hQM⟩ := common_of_cross_ne_zero L M hc
      refine ⟨Q, hQL, hQM, fun hQ => ?_⟩
      have hmem : Q ∈ (M.points ∩ Pl) ∩ (L.points ∩ Pl) := ⟨⟨hQM, hQ⟩, ⟨hQL, hQ⟩⟩
      rw [h] at hmem
      exact hmem
  · rintro (hc | ⟨Q, hQL, hQM, hQ⟩)
    · apply Set.eq_empty_of_forall_notMem
      rintro X ⟨⟨hXM, -⟩, ⟨hXL, -⟩⟩
      exact no_common_of_cross_eq_zero L M hL hc hP hPL hXL hXM
    · apply Set.eq_empty_of_forall_notMem
      rintro X ⟨⟨hXM, hX⟩, ⟨hXL, -⟩⟩
      by_cases hXQ : X = Q
      · exact hQ (hXQ ▸ hX)
      · apply hPL
        rw [points_eq_of_two_common L M hXQ hXL hQL hXM hQM]
        exact hP
end ParallelPostulate.HyperbolicPlane
