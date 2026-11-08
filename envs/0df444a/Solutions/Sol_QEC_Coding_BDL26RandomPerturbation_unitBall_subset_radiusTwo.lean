-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.unitBall_subset_radiusTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:33:41.103134+00:00
-- url     : https://prove2.me/submissions/3f738b91-eefd-4bf8-99a4-d2b99e8d905d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (center net : Space) (h : dist center net ≤ 1) :
    Metric.closedBall center 1 ⊆ Metric.closedBall net 2 := by
  intro p hp
  have hp' : dist p center ≤ 1 := hp
  have ht := dist_triangle p center net
  change dist p net ≤ 2
  linarith
end QEC.Coding.BDL26RandomPerturbation
