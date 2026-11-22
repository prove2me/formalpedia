-- Prove2me | solution 1 for Paper.Hypergraph.levelMeasure_Icc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:46.702973+00:00
-- url     : https://prove2.me/submissions/429f501c-2143-4ed4-9cfc-89a8bc1ee5c5

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (a b : ℝ) : levelMeasure.real (Icc a b) ≤ max (b - a) 0 := by
  calc
    _ = volume.real (Icc a b ∩ Ioo 0 1) := measureReal_restrict_apply measurableSet_Icc
    _ ≤ volume.real (Icc a b) := measureReal_mono inter_subset_left isCompact_Icc.measure_ne_top
    _ = _ := Real.volume_real_Icc
end Paper.Hypergraph
