-- Prove2me | solution 1 for QEC.Locality.vertexScore_eq_cast_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:00:34.271324+00:00
-- url     : https://prove2.me/submissions/5c5ec299-37b2-4ab8-9871-f36c3cf3f94a

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
    vertexScore w r points t = (vertexBadCount w r points t : ℝ) := by
  rw [vertexScore, vertexBadCount, Finset.sum_boole]
end QEC.Locality
