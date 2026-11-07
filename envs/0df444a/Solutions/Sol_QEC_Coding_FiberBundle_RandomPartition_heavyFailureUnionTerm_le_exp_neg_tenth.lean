-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.heavyFailureUnionTerm_le_exp_neg_tenth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:09.697509+00:00
-- url     : https://prove2.me/submissions/63157b83-085e-40da-b493-3e2263da4a50

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_heavyFailureUnionTerm_le_exp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall :
      (100 : Real) * typeCount ≤ r)
    (hScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta) :
    (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) *
        Real.exp (-3 * (r : Real)) ≤
      Real.exp (-(r : Real) / 10) := by
  have hEnvelope :=
    heavyFailureUnionTerm_le_exp r Delta typeCount hDelta
  apply hEnvelope.trans
  apply Real.exp_le_exp.mpr
  have hDeltaReal : (0 : Real) < Delta := by exact_mod_cast hDelta
  have hLogDelta : 0 ≤ Real.log (Delta : Real) :=
    Real.log_nonneg (by exact_mod_cast hDeltaOne)
  have hLogTwo : Real.log 2 ≤ (7 : Real) / 10 := by
    exact le_trans (le_of_lt Real.log_two_lt_d9) (by norm_num)
  have hK :
      ((((8 * r) / Delta : Nat) : Real)) ≤
        ((8 * r : Nat) : Real) / Delta :=
    Nat.cast_div_le
  have hKLog :
      ((((8 * r) / Delta : Nat) : Real) * Real.log Delta) ≤
        (((8 * r : Nat) : Real) / Delta) * Real.log Delta :=
    mul_le_mul_of_nonneg_right hK hLogDelta
  have hBinary :
      (((4 * r + typeCount : Nat) : Real) * Real.log 2) ≤
        (((4 * r + typeCount : Nat) : Real) * ((7 : Real) / 10)) :=
    mul_le_mul_of_nonneg_left hLogTwo (by positivity)
  have hBinary' :
      (((4 * r + typeCount : Nat) : Real) * Real.log 2) ≤
        (14 : Real) / 5 * r + (7 : Real) / 10 * typeCount := by
    calc
      _ ≤
          (((4 * r + typeCount : Nat) : Real) *
            ((7 : Real) / 10)) := hBinary
      _ = _ := by push_cast; ring
  have hNeighborRaw :
      ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r) / Delta : Nat) : Real) * Real.log Delta) ≤
        ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r : Nat) : Real) / Delta) * Real.log Delta) := by
    gcongr
  have hQ :
      (typeCount : Real) * (1 + 2 * Real.log Delta) / Delta ≤
        (1 : Real) / 100 := by
    apply (div_le_iff₀ hDeltaReal).2
    nlinarith
  have hNeighborEq :
      ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r : Nat) : Real) / Delta) * Real.log Delta) =
        8 * (r : Real) *
          ((typeCount : Real) * (1 + 2 * Real.log Delta) / Delta) := by
    push_cast
    field_simp
    ring
  have hNeighbor :
      ((2 * typeCount : Nat) : Real) *
          ((((4 * r : Nat) : Real) / Delta) +
            (((8 * r) / Delta : Nat) : Real) * Real.log Delta) ≤
        (2 : Real) / 25 * r := by
    calc
      _ ≤
          ((2 * typeCount : Nat) : Real) *
            ((((4 * r : Nat) : Real) / Delta) +
              (((8 * r : Nat) : Real) / Delta) *
                Real.log Delta) := hNeighborRaw
      _ =
          8 * (r : Real) *
            ((typeCount : Real) *
              (1 + 2 * Real.log Delta) / Delta) := hNeighborEq
      _ ≤ 8 * (r : Real) * ((1 : Real) / 100) := by
        gcongr
      _ = (2 : Real) / 25 * r := by ring
  calc
    (((4 * r + typeCount : Nat) : Real) * Real.log 2) +
          ((2 * typeCount : Nat) : Real) *
            ((((4 * r : Nat) : Real) / Delta) +
              (((8 * r) / Delta : Nat) : Real) * Real.log Delta) -
        3 * (r : Real) ≤
      ((14 : Real) / 5 * r + (7 : Real) / 10 * typeCount) +
        (2 : Real) / 25 * r - 3 * r := by
      gcongr
    _ ≤ -(r : Real) / 10 := by
      nlinarith
end QEC.Coding.FiberBundle.RandomPartition
