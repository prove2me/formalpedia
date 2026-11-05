-- Prove2me | solution 1 for Sat3.InRateTM.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:19.171205+00:00
-- url     : https://prove2.me/submissions/93633f1d-bfff-41a0-9f0e-c31b7f1e8bd9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_rateBound_anti
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
namespace InRateTM
theorem _root_.solution {c c' : ℝ} (h : InRateTM c) (hc : c' ≤ c) : InRateTM c' := by
  obtain ⟨M, C, hfin, hM⟩ := h
  exact ⟨M, C, hfin, hM.mono (rateBound_anti C hc)⟩
end InRateTM
end Sat3
