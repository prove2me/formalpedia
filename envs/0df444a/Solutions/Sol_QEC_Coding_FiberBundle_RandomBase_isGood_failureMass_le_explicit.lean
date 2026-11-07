-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.isGood_failureMass_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:48:18.229795+00:00
-- url     : https://prove2.me/submissions/7ea72dd4-3eda-4715-b776-849190ed51bb

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_linearDistance_failureMass_le_split
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_isGood_failureMass_le_components
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_degreeWindows_failureMass_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_fullRowRank_failureMass_le_split


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsGood (Delta := Delta) sample) ≤
      ENNReal.ofReal
          ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
          (2 : ENNReal) ^ (3 * r) *
            (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) *
            (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r)) := by
  calc
    _ ≤
        failureMass
            (distribution r Delta hDelta)
            (fun sample => HasDegreeWindows (Delta := Delta) sample) +
          failureMass
            (distribution r Delta hDelta)
            (@HasFullRowRank r) +
          failureMass
            (distribution r Delta hDelta)
            (@HasLinearDistance r) :=
      isGood_failureMass_le_components r Delta hDelta
    _ ≤ _ := by
      gcongr
      · exact degreeWindows_failureMass_le r Delta hr hDelta
      · exact fullRowRank_failureMass_le_split
          r Delta hr hDelta hHalf
      · exact linearDistance_failureMass_le_split
          r Delta hr hDelta hHalf
end QEC.Coding.FiberBundle.RandomBase
