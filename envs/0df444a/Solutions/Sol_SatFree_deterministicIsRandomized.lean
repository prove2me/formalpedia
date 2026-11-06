-- Prove2me | solution 1 for SatFree.deterministicIsRandomized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:05:32.245022+00:00
-- url     : https://prove2.me/submissions/2545e56a-ebcb-4241-a516-533833a08bea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random
import Theorems.Thm_SatFree_noBits

set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : DeterministicIsRandomized := fun _ M t h n φ hφ => by
  obtain ⟨b, hb, ev⟩ := h n φ hφ
  obtain ⟨h1, h2⟩ := noBits M (enc φ) b (t n) ev
  exact ⟨h1, b, hb, h2⟩
end SatFree
