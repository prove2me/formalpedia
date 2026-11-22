-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.misses_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:09:23.020993+00:00
-- url     : https://prove2.me/submissions/08e5f91f-9358-43cb-a1c3-5a0c08990991

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_zero_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_rebase_zero_ne_one
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_cross_rebase
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_points_eq_through
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_points_eq_of_cross_eq_zero
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_miss_iff
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_euclid_misses
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_toward_misses

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (Pl : Set (K × K)) (L : Dim K) (hL : L.zero ≠ L.one) {P : K × K}
    (hP : P ∈ Pl) (hPL : P ∉ L.points) (S : Set (K × K)) :
    Misses Pl L P S ↔ S = euclid Pl L P ∨ ∃ t : K, L.pt t ∉ Pl ∧ S = toward Pl L P t := by
  constructor
  · rintro ⟨⟨M, hM, rfl, -⟩, hPS, hmiss⟩
    rcases (miss_iff Pl L M hL hPS.1 hPL).mp hmiss with hc | ⟨Q, ⟨t, rfl⟩, hQM, hQ⟩
    · left
      unfold euclid
      rw [points_eq_of_cross_eq_zero L M (L.rebase P) hL hM (L.rebase_zero_ne_one hL P) hc
        (L.cross_rebase P) hPS.1 (L.rebase P).zero_mem]
    · right
      refine ⟨t, hQ, ?_⟩
      have hne : P ≠ L.pt t := fun h => hQ (h ▸ hP)
      unfold toward
      rw [M.points_eq_through hPS.1 hQM hne]
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact euclid_misses Pl L hL hP hPL
    · exact toward_misses Pl L hL hP hPL ht
end ParallelPostulate.HyperbolicPlane
