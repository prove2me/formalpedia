-- Prove2me | solution 1 for Sat3.DecidesTM.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:20:39.287554+00:00
-- url     : https://prove2.me/submissions/7c33c140-6634-4f5b-bdb8-c695153f453b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ToTuring_EndLemmas

set_option autoImplicit false
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
namespace DecidesTM
theorem _root_.solution {M : TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (h : DecidesTM M t)
    (ht : ∀ n, t n ≤ t' n) : DecidesTM M t' := by
  intro n φ hφ
  obtain ⟨b, hb, ⟨ev⟩⟩ := h n φ hφ
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (ht n)⟩⟩⟩
end DecidesTM
end Sat3
