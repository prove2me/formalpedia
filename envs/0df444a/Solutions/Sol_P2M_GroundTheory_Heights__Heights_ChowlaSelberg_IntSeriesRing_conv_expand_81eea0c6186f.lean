-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_expand_81eea0c6186f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:29.009976+00:00
-- url     : https://prove2.me/submissions/c03c97ad-0455-47d1-bdbc-e5169e83cbf9

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
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) {F : PowerSeries ℤ} {r : ℝ}
    (hF : IntSeriesConv F (r ^ p)) : IntSeriesConv (expand p hp F) r := by
  unfold IntSeriesConv at *
  refine ((mul_left_injective' hp).summable_iff ?_).mp ?_
  · rintro n hn
    have h : ¬ p ∣ n := fun ⟨m, hm⟩ ↦ hn ⟨m, hm.symm⟩
    simp [coeff_expand_of_not_dvd p hp _ h]
  · simpa [Function.comp_def, coeff_expand_mul, pow_mul] using hF
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
