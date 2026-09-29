-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_config_continuous_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:34:14.676234+00:00
-- url     : https://prove2.me/submissions/752d79a0-c247-4362-8e83-d221695c655a

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_continuous_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma continuous_leftBraidConfig_v1 (n : ℕ) (i j : Fin (n - 1)) :
    Continuous (leftBraidConfig n i j) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun k =>
    thm_3_15_adjacent_raw_continuous_v1.1 n i j k

lemma continuous_rightBraidConfig_v1 (n : ℕ) (i j : Fin (n - 1)) :
    Continuous (rightBraidConfig n i j) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun k =>
    thm_3_15_adjacent_raw_continuous_v1.2.1 n i j k

lemma continuous_outerRotateConfig_v1 {n : ℕ} (i : Fin (n - 1))
    (hi2 : (i : ℕ) + 2 < n) :
    Continuous (outerRotateConfig i hi2) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun k =>
    thm_3_15_adjacent_raw_continuous_v1.2.2 n i k

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    (∀ (n : ℕ) (i j : Fin (n - 1)), Continuous (leftBraidConfig n i j)) ∧
    (∀ (n : ℕ) (i j : Fin (n - 1)), Continuous (rightBraidConfig n i j)) ∧
    (∀ {n : ℕ} (i : Fin (n - 1)) (hi2 : (i : ℕ) + 2 < n),
      Continuous (outerRotateConfig i hi2)) := by
  exact ⟨continuous_leftBraidConfig_v1,
    ⟨continuous_rightBraidConfig_v1, continuous_outerRotateConfig_v1⟩⟩
