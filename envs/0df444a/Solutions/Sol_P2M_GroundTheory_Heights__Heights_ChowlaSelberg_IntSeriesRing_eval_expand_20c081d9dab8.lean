-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_expand_20c081d9dab8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:31.646874+00:00
-- url     : https://prove2.me/submissions/9189d35f-c8e0-4e4e-96ae-a42b47d04df3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_mul_left_injective__8c30cfed51d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) (F : PowerSeries ℤ) (z : ℂ) :
    intSeriesEval (expand p hp F) z = intSeriesEval F (z ^ p) := by
  unfold intSeriesEval
  rw [← (mul_left_injective' hp).tsum_eq]
  · simp [coeff_expand_mul, pow_mul]
  · intro n hn
    by_contra h
    have h' : ¬ p ∣ n := fun ⟨m, hm⟩ ↦ h ⟨m, hm.symm⟩
    exact hn (by simp [coeff_expand_of_not_dvd p hp _ h'])
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
