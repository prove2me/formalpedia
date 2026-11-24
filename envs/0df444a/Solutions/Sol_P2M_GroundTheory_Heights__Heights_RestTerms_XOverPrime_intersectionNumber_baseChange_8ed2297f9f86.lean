-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_XOverPrime_intersectionNumber_baseChange_8ed2297f9f86
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:30.21688+00:00
-- url     : https://prove2.me/submissions/77f5ad1e-e0f3-4b2d-b747-d91c50ff30dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XBound_intersectionNumber_baseChange_3674cb61fc35

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace XOverPrime
theorem _root_.solution : XOverPrime.Statement := by
  intro f r a B₀ p hf hN hB hp
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hX := (XBound.intersectionNumber_baseChange r a hN)
  have hX2 : (restX r a : ℝ) ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := hX.1.trans hX.2
  have hN2 : 0 < ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hp4 : 4 * ((r + a : ℕ) : ℝ) ^ 2 < p := by nlinarith
  have hp0 : 0 < p := lt_trans (by positivity) hp4
  rw [div_le_iff₀ hp0]
  nlinarith
end XOverPrime
end GroundTheory.Heights₂.Heights.RestTerms
