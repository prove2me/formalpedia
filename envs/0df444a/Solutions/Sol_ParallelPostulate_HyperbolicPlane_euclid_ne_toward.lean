-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.euclid_ne_toward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:08:13.606243+00:00
-- url     : https://prove2.me/submissions/46395f16-dea5-4715-8c0f-d8560dc4c2ee

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_zero_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_one_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_rebase_zero_ne_one
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_cross_rebase
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_injective
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
theorem _root_.solution (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) (t : K) :
    euclid Pl L P ≠ toward Pl L P t := by
  intro h
  obtain ⟨r, hr, hX⟩ := hopen (L.rebase P) hP
  have hN := L.rebase_zero_ne_one hL P
  have hX' : (L.rebase P).pt r ∈ toward Pl L P t := by
    rw [← h]
    exact ⟨⟨r, rfl⟩, hX⟩
  have hPX : P ≠ (L.rebase P).pt r := fun h' =>
    hr ((L.rebase P).pt_injective hN ((L.rebase P).pt_zero.trans h')).symm
  have hsame : (L.rebase P).points = (Dim.mk P (L.pt t)).points :=
    points_eq_of_two_common _ _ hPX (L.rebase P).zero_mem ⟨r, rfl⟩
      (Dim.mk P (L.pt t)).zero_mem hX'.1
  have hQ : L.pt t ∈ (L.rebase P).points := by
    rw [hsame]
    exact (Dim.mk P (L.pt t)).one_mem
  exact no_common_of_cross_eq_zero L (L.rebase P) hL (L.cross_rebase P)
    (L.rebase P).zero_mem hPL ⟨t, rfl⟩ hQ
end ParallelPostulate.HyperbolicPlane
