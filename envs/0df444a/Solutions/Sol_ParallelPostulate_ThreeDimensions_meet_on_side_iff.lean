-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.meet_on_side_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:13:08.912743+00:00
-- url     : https://prove2.me/submissions/9c72e317-dbfe-43bc-abe6-713f3cc76e1c

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_fifth_postulate
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_the_other_side
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_ne
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_meet_unique
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_never_meet_of_two_right_angles


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ 0 < cross F.b.dir F.c.dir := by
  constructor
  · rintro ⟨t, u, ht, -, h⟩
    rcases lt_trichotomy (cross F.b.dir F.c.dir) 0 with hneg | hzero | hpos
    · obtain ⟨t', u', ht', -, h', -⟩ := meet_on_the_other_side F hb hc hneg
      have htt := (F.meet_unique hneg.ne h h').1
      rw [htt] at ht
      exact absurd ht (lt_asymm ht')
    · exact absurd h (F.never_meet_of_two_right_angles hc.ne' hzero t u)
    · exact hpos
  · intro hsum
    obtain ⟨t, u, ht, hu, h, -⟩ := fifth_postulate F hb hc hsum
    exact ⟨t, u, ht, hu, h⟩
end ParallelPostulate.ThreeDimensions
