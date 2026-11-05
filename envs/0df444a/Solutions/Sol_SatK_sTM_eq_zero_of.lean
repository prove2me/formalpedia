-- Prove2me | solution 1 for SatK.sTM_eq_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:02:30.382982+00:00
-- url     : https://prove2.me/submissions/d9d0cb3f-d95a-4e37-b824-7b6f63d870a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_WidthK_Top_EndLemmas

set_option autoImplicit false
section
open SatK
open scoped NNReal ENNReal
namespace SatK
theorem _root_.solution {k : ℕ} (h : ∀ δ : ℝ≥0, 0 < δ → InTimeTM k δ) : sTM k = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  exact iInf₂_le ε (h ε hε)
end SatK
