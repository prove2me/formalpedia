-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_interp_one_fun_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T12:13:08.420968+00:00
-- url     : https://prove2.me/submissions/77353953-6905-487d-bfad-acc6a2841fe9

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_one_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_one_endpoint_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightInterp_hi2_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : (i : ℕ) + 2 < n := by
  have hj := j.isLt
  omega

lemma rightInterp_one_fun_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u : unitInterval) :
    (rightOuterInterpConfig i j hji u 1).1 =
      (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  funext k
  have hi2 := rightInterp_hi2_v1 i j hji
  have hR := (thm_3_15_adjacent_word_one_endpoints_v1 i j hji).2
  have hO := thm_3_15_adjacent_outer_one_endpoint_v1 i j hji hi2
  change braidInterp (u : ℝ) (rightBraidFun n i j 1 k)
    (outerRotateFun n i 1 k) =
      ((baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j)) k
  rw [congrFun hR k, congrFun hO k]
  unfold braidInterp
  module

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1)
      (u : unitInterval),
      (rightOuterInterpConfig i j hji u 1).1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  exact rightInterp_one_fun_v1
