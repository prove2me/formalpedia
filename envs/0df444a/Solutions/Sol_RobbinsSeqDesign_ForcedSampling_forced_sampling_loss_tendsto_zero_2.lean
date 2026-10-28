-- Prove2me | solution 2 for RobbinsSeqDesign.ForcedSampling.forced_sampling_loss_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:32:08.436415+00:00
-- url     : https://prove2.me/submissions/3f26158b-5809-4343-98d1-e004d231c67e

import Mathlib
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Rule
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Loss
import Theorems.Thm_RobbinsSeqDesign_ForcedSampling_expected_average_tendsto_max

set_option autoImplicit false
open RobbinsSeqDesign.ForcedSampling
open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

-- carved from submission 925993d1-11a4-44d6-a435-8a29666a344b, lines 1564-1577

theorem solution (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    Tendsto (fun n : ℕ => loss ν (rule σ) n) atTop (𝓝 0) := by
  have h := RobbinsSeqDesign.ForcedSampling.expected_average_tendsto_max ν hint σ
  have h2 := (tendsto_const_nhds (x := max (banditArmMean ν 0) (banditArmMean ν 1))).sub h
  simpa [loss] using h2
