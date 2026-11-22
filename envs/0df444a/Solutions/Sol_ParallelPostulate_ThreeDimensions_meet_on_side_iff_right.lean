-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.meet_on_side_iff_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:09.584171+00:00
-- url     : https://prove2.me/submissions/050e0830-0b29-4679-986b-96939a3779b7

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_side_iff
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_cross
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_side


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ cross F.b.dir F.c.dir < 0 := by
  have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hc
  have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hb
  have h := meet_on_side_iff F.reverse hb' hc'
  rw [F.reverse_cross, neg_pos] at h
  rw [← h]
  constructor
  · rintro ⟨t, u, ht, hu, e⟩
    exact ⟨u, t, hu, ht, e.symm⟩
  · rintro ⟨t, u, ht, hu, e⟩
    exact ⟨u, t, hu, ht, e.symm⟩
end ParallelPostulate.ThreeDimensions
