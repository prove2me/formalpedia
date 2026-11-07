-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.isFullyGood_failureMass_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:40.452824+00:00
-- url     : https://prove2.me/submissions/9496b7dc-99a7-4db2-a440-2fba470a2a4e

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_strongSmallSetExpansion_failureMass_le_binomial
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_isFullyGood_failureMass_le_components
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_isGood_failureMass_le_explicit


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
        (fun sample => IsFullyGood (Delta := Delta) sample) ≤
      (ENNReal.ofReal
          ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
          (2 : ENNReal) ^ (3 * r) *
            (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) *
            (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r))) +
      ((1 + ENNReal.ofReal
        (Real.exp (-(Delta : Real) / 1000))) ^ (3 * r) - 1) := by
  calc
    _ ≤ failureMass
          (distribution r Delta hDelta)
          (fun sample => IsGood (Delta := Delta) sample) +
        failureMass
          (distribution r Delta hDelta)
          (fun sample =>
            HasStrongSmallSetExpansion (Delta := Delta) sample) :=
      isFullyGood_failureMass_le_components r Delta hDelta
    _ ≤ _ := by
      gcongr
      · exact isGood_failureMass_le_explicit
          r Delta hr hDelta hHalf
      · exact strongSmallSetExpansion_failureMass_le_binomial
          r Delta hr hDelta
end QEC.Coding.FiberBundle.RandomBase
