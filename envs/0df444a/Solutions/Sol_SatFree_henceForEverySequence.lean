-- Prove2me | solution 1 for SatFree.henceForEverySequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:21.831014+00:00
-- url     : https://prove2.me/submissions/8ceb2d39-b594-4b5f-9a09-107b993f94f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Order

set_option autoImplicit false
section
section
open SatFree
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : HenceForEverySequence := fun u hu => by
  have hm : Monotone u := monotone_nat_of_le_succ hu
  have hs : (⨆ (k : ℕ) (_ : 3 ≤ k), u k) = ⨆ k : ℕ, u k :=
    le_antisymm (iSup₂_le fun k _ => le_iSup u k)
      (iSup_le fun k => (hm (le_max_left k 3)).trans (le_iSup₂ (f := fun (k : ℕ) (_ : 3 ≤ k) => u k) (max k 3) (le_max_right k 3)))
  refine ⟨?_, fun h => h 3 le_rfl, fun h k hk => h.trans_le (hm hk)⟩
  rw [hs]
  exact tendsto_atTop_iSup hm
end SatFree
