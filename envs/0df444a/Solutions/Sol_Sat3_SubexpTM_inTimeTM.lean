-- Prove2me | solution 1 for Sat3.SubexpTM.inTimeTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:33:52.396361+00:00
-- url     : https://prove2.me/submissions/25837361-b8ed-44cc-9015-6322a3f0b5b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
namespace SubexpTM
theorem _root_.solution (h : SubexpTM) {δ : ℝ≥0} (hδ : 0 < δ) : InTimeTM δ := by
  obtain ⟨M, hfin, hM⟩ := h
  obtain ⟨c, hc⟩ := hM δ hδ
  exact ⟨M, c, hfin, hc⟩
end SubexpTM
end Sat3
