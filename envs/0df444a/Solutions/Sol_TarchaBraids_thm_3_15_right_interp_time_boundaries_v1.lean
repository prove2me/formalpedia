-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_interp_time_boundaries_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T12:51:08.043862+00:00
-- url     : https://prove2.me/submissions/988a517a-5426-4093-9845-6908620f828b

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_zero_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_one_fun_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightInterp_zero_time_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u : unitInterval) :
    configProj n (rightOuterInterpConfig i j hji u 0) = baseUnordered n := by
  change configProj n (rightOuterInterpConfig i j hji u 0) =
    configProj n (baseOrdered n)
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  have hR := thm_3_15_adjacent_raw_zero_endpoints_v1.2.1 n i j
  have hO := thm_3_15_adjacent_raw_zero_endpoints_v1.2.2 n i
  change braidInterp (u : ℝ) (rightBraidFun n i j 0 k)
    (outerRotateFun n i 0 k) = (baseOrdered n).1 k
  rw [congrFun hR k, congrFun hO k]
  unfold braidInterp
  module

lemma rightInterp_one_time_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u : unitInterval) :
    configProj n (rightOuterInterpConfig i j hji u 1) = baseUnordered n := by
  change Quotient.mk (configSetoid n) (rightOuterInterpConfig i j hji u 1) =
    Quotient.mk (configSetoid n) (baseOrdered n)
  have h : configProj n (baseOrdered n) =
      configProj n (rightOuterInterpConfig i j hji u 1) :=
    Quotient.sound ⟨Equiv.swap (strandIdx i) (strandIdxSucc j),
      thm_3_15_right_interp_one_fun_v1 i j hji u⟩
  exact h.symm

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 0) = baseUnordered n) ∧
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 1) = baseUnordered n) := by
  intro n i j hji
  exact ⟨rightInterp_zero_time_v1 i j hji,
    rightInterp_one_time_v1 i j hji⟩
