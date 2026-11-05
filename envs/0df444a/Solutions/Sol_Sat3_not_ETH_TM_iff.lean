-- Prove2me | solution 1 for Sat3.not_ETH_TM_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:32:46.845804+00:00
-- url     : https://prove2.me/submissions/82680d31-a869-4f20-9fc7-af1f14c8552e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ToTuring_EndLemmas
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono

set_option autoImplicit false
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution : ¬ETH_TM ↔ ∀ δ : ℝ≥0, 0 < δ → InTimeTM δ := by
  refine ⟨fun h δ hδ => ?_, fun h hpos => ?_⟩
  · have hlt : s₃TM < δ := (not_lt.1 h).trans_lt (ENNReal.coe_pos.2 hδ)
    simp only [s₃TM, iInf_lt_iff] at hlt
    obtain ⟨δ₀, h₀, hlt⟩ := hlt
    exact h₀.mono (ENNReal.coe_le_coe.1 hlt.le)
  · obtain ⟨r, hr₀, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
    exact (show s₃TM ≤ r from iInf₂_le r (h r (ENNReal.coe_pos.1 hr₀))).not_gt hr
end Sat3
