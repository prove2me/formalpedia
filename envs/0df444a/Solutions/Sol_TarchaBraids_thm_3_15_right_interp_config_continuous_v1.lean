-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_interp_config_continuous_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T12:00:32.698405+00:00
-- url     : https://prove2.me/submissions/fab81a1d-1d09-454d-8aba-c51ad8db99ce

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_continuous_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma continuous_rightOuterInterpConfig_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    Continuous (fun z : unitInterval × unitInterval =>
      rightOuterInterpConfig i j hji z.1 z.2) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun k => ?_
  change Continuous (fun z : unitInterval × unitInterval =>
    rightOuterInterpFun n i j (z.1 : ℝ) (z.2 : ℝ) k)
  have hu : Continuous (fun z : unitInterval × unitInterval => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hright : Continuous (fun z : unitInterval × unitInterval =>
      rightBraidFun n i j (z.2 : ℝ) k) :=
    (thm_3_15_adjacent_raw_continuous_v1.2.1 n i j k).comp
      (continuous_subtype_val.comp continuous_snd)
  have houter : Continuous (fun z : unitInterval × unitInterval =>
      outerRotateFun n i (z.2 : ℝ) k) :=
    (thm_3_15_adjacent_raw_continuous_v1.2.2 n i k).comp
      (continuous_subtype_val.comp continuous_snd)
  unfold rightOuterInterpFun braidInterp
  exact ((continuous_const.sub hu).smul hright).add (hu.smul houter)

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Continuous (fun z : unitInterval × unitInterval =>
        rightOuterInterpConfig i j hji z.1 z.2) := by
  exact continuous_rightOuterInterpConfig_v1
