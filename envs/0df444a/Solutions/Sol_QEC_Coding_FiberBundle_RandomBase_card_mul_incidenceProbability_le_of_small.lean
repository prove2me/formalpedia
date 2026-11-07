-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.card_mul_incidenceProbability_le_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:51:55.1222+00:00
-- url     : https://prove2.me/submissions/ff721a71-70b6-4635-a49d-992697ade3a6

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_expected_degree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (S.card : NNReal) * incidenceProbability (4 * r) Delta ≤
      (3 : NNReal) / 400000 := by
  have hExpected :=
    check_expected_degree r Delta hr
  have hSmallReal :
      (100000 : Real) * Delta * S.card ≤ 3 * r := by
    exact_mod_cast hSmall
  have hrReal : (0 : Real) < r := by
    exact_mod_cast hr
  change
    (S.card : Real) *
        (incidenceProbability (4 * r) Delta).toReal ≤
      (3 : Real) / 400000
  rw [mul_comm]
  rw [← hExpected] at hSmallReal
  norm_num [Nat.cast_mul] at hSmallReal
  nlinarith
end QEC.Coding.FiberBundle.RandomBase
