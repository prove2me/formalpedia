-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.smallNeighborhood_eventMass_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:38.874267+00:00
-- url     : https://prove2.me/submissions/4a3ee18f-0870-4306-9dd2-08b498ba3009

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_twenty_nineteenths_pow_le_exp
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      ENNReal.ofReal
        (Real.exp
          ((cutoff : Real) / 19 -
            (399997 : Real) * Delta * S.card / 8000000)) := by
  let tailMass : ENNReal :=
    eventMass
      (distribution r Delta hDelta)
      (fun sample =>
        (checkSetNeighborhood sample S).card ≤ cutoff)
  have hWeighted :
      ((19 : ENNReal) / 20) ^ cutoff * tailMass ≤
        ENNReal.ofReal
          (Real.exp
            (-((399997 : Real) * Delta * S.card / 8000000))) := by
    exact nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp
      r Delta hr hDelta S hSmall cutoff
  have hReciprocalEq :
      (((20 : NNReal) / 19 : NNReal) : ENNReal) =
        (20 : ENNReal) / 19 :=
    ENNReal.coe_div (by norm_num)
  have hWeightEq :
      (((19 : NNReal) / 20 : NNReal) : ENNReal) =
        (19 : ENNReal) / 20 :=
    ENNReal.coe_div (by norm_num)
  have hCancel :
      (20 : ENNReal) / 19 * ((19 : ENNReal) / 20) = 1 := by
    rw [← hReciprocalEq, ← hWeightEq, ← ENNReal.coe_mul, ← ENNReal.coe_one]
    norm_num
  have hIdentity :
      ((20 : ENNReal) / 19) ^ cutoff *
          (((19 : ENNReal) / 20) ^ cutoff * tailMass) =
        tailMass := by
    rw [← mul_assoc, ← mul_pow, hCancel, one_pow, one_mul]
  calc
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤ cutoff) =
        tailMass := rfl
    _ = ((20 : ENNReal) / 19) ^ cutoff *
          (((19 : ENNReal) / 20) ^ cutoff * tailMass) := hIdentity.symm
    _ ≤ ((20 : ENNReal) / 19) ^ cutoff *
          ENNReal.ofReal
            (Real.exp
              (-((399997 : Real) * Delta * S.card / 8000000))) := by
      exact mul_le_mul_of_nonneg_left hWeighted (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp ((cutoff : Real) / 19)) *
          ENNReal.ofReal
            (Real.exp
              (-((399997 : Real) * Delta * S.card / 8000000))) := by
      exact mul_le_mul_of_nonneg_right
        (twenty_nineteenths_pow_le_exp cutoff)
        (by positivity)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_add]
      congr 1
end QEC.Coding.FiberBundle.RandomBase
