-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_mul_left_injective__8c30cfed51d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:58.739805+00:00
-- url     : https://prove2.me/submissions/83f40953-8ce8-4d18-b46e-aee07a13b54d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing

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
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) : Function.Injective fun m : ℕ ↦ p * m :=
  fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
