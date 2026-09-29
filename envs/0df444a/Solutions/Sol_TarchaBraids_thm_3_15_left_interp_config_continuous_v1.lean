-- Prove2me | solution 1 for TarchaBraids.thm_3_15_left_interp_config_continuous_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T09:13:40.894441+00:00
-- url     : https://prove2.me/submissions/da364946-084c-4516-97d5-51deff48f004

import Mathlib
import Definitions.Def_TarchaBraids_left_interp_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_continuous_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma continuous_leftOuterInterpConfig_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    Continuous (fun z : unitInterval × unitInterval =>
      leftOuterInterpConfig i j hji z.1 z.2) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun k => ?_
  change Continuous (fun z : unitInterval × unitInterval =>
    leftOuterInterpFun n i j (z.1 : ℝ) (z.2 : ℝ) k)
  have hu : Continuous (fun z : unitInterval × unitInterval => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hleft : Continuous (fun z : unitInterval × unitInterval =>
      leftBraidFun n i j (z.2 : ℝ) k) :=
    (thm_3_15_adjacent_raw_continuous_v1.1 n i j k).comp
      (continuous_subtype_val.comp continuous_snd)
  have houter : Continuous (fun z : unitInterval × unitInterval =>
      outerRotateFun n i (z.2 : ℝ) k) :=
    (thm_3_15_adjacent_raw_continuous_v1.2.2 n i k).comp
      (continuous_subtype_val.comp continuous_snd)
  unfold leftOuterInterpFun braidInterp
  exact ((continuous_const.sub hu).smul hleft).add (hu.smul houter)

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Continuous (fun z : unitInterval × unitInterval =>
        leftOuterInterpConfig i j hji z.1 z.2) := by
  exact continuous_leftOuterInterpConfig_v1
