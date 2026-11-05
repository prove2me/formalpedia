-- Prove2me | solution 1 for SingleBitPieces.Level.Pieces.sum_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:29:35.95863+00:00
-- url     : https://prove2.me/submissions/ca2c54bc-1c0d-44da-ac3c-7426b1fcb1bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_ClauseBound_Alg_Grid
import Definitions.Def_PaddedDescent_F_FuelCert
import Mathlib.Tactic
import Definitions.Def_SingleBitPieces_Level_Pieces
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset
open SingleBitPieces.Level.Pieces
namespace SingleBitPieces.Level.Pieces
theorem _root_.solution (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Fin c → Bool, G (List.ofFn θ) = ∑ w ∈ words c, G w := by
  refine sum_bij (fun θ _ => List.ofFn θ) (fun θ _ => mem_words.2 List.length_ofFn) (fun θ _ θ' _ h => List.ofFn_injective h)
    (fun w hw => ?_) fun θ _ => rfl
  obtain rfl := mem_words.1 hw
  exact ⟨fun t => w[t], mem_univ _, List.ofFn_getElem⟩
end SingleBitPieces.Level.Pieces
