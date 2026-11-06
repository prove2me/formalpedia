-- Prove2me | solution 1 for QEC.Locality.edgeScore_eq_cast_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:00:40.937417+00:00
-- url     : https://prove2.me/submissions/3374f3fe-ee5b-4294-9fab-c94f7944ed7d

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) :
    edgeScore w r points t = (edgeBadCount w r points t : ℝ) := by
  rw [edgeScore, edgeBadCount, Finset.sum_boole]
end QEC.Locality
