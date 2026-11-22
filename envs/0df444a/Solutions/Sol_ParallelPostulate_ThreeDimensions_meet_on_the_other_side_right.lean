-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.meet_on_the_other_side_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:09.015177+00:00
-- url     : https://prove2.me/submissions/e2029222-8da9-406e-8462-438efa668503

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
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_meet_eq
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_b_one
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_b_pt
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_c_one


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : cross F.a.dir F.c.dir / cross F.b.dir F.c.dir < 0 := div_neg_of_neg_of_pos hc hsum
  refine ⟨_, _, ht, div_neg_of_neg_of_pos hb hsum, F.meet_eq hsum.ne', ?_⟩
  rw [F.side_b_pt]
  exact mul_pos_of_neg_of_neg ht hb
end ParallelPostulate.ThreeDimensions
