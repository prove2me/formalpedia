-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.rowParityZero_eventMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:53.035469+00:00
-- url     : https://prove2.me/submissions/a75ec252-9b7c-40dd-8362-787fbd594cc7

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_rowParityZero_measureReal
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_eq_toMeasure


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    eventMass
        (rowDistribution r Delta hDelta)
        (RowParityZero A) =
      ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2) := by
  classical
  calc
    _ = (rowDistribution r Delta hDelta).toMeasure
        {row | RowParityZero A row} :=
      eventMass_eq_toMeasure _ _
    _ = ENNReal.ofReal
        ((rowDistribution r Delta hDelta).toMeasure.real
          {row | RowParityZero A row}) := by
      rw [ofReal_measureReal]
    _ = _ := by
      rw [rowParityZero_measureReal r Delta hDelta A]
end QEC.Coding.FiberBundle.RandomBase
