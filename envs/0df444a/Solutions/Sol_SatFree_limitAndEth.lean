-- Prove2me | solution 1 for SatFree.limitAndEth
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:21:02.462425+00:00
-- url     : https://prove2.me/submissions/be708f8c-14d2-4669-b2be-4ed405e65601

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

private theorem satFree_sameMachine : SameMachine :=
  fun k _ _ h n φ hφ => h n φ ⟨fun C hC => (hφ.1 C hC).trans (Nat.le_succ k), hφ.2⟩

private theorem satFree_increasing : Increasing := fun k =>
  le_iInf₂ fun δ hδ => iInf₂_le δ (by
    obtain ⟨M, c, hfin, h⟩ := hδ
    exact ⟨M, c, hfin, satFree_sameMachine k M _ h⟩)

private theorem satFree_henceForEverySequence : HenceForEverySequence := fun u hu => by
  have hm : Monotone u := monotone_nat_of_le_succ hu
  have hs : (⨆ (k : ℕ) (_ : 3 ≤ k), u k) = ⨆ k : ℕ, u k :=
    le_antisymm (iSup₂_le fun k _ => le_iSup u k)
      (iSup_le fun k => (hm (le_max_left k 3)).trans
        (le_iSup₂ (f := fun (k : ℕ) (_ : 3 ≤ k) => u k) (max k 3) (le_max_right k 3)))
  refine ⟨?_, fun h => h 3 le_rfl, fun h k hk => h.trans_le (hm hk)⟩
  rw [hs]
  exact tendsto_atTop_iSup hm

theorem solution : LimitAndEth := satFree_henceForEverySequence s satFree_increasing
