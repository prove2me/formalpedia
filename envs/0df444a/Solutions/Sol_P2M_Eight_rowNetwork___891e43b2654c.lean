-- Prove2me | solution 1 for P2M_Eight_rowNetwork___891e43b2654c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:23.433772+00:00
-- url     : https://prove2.me/submissions/d76fbfb2-e6bc-4b77-9aa9-3fca783592a1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Eight_rowCut_factors
import Theorems.Thm_P2M_Groundwork_Grid_rowNet___43280a58588e
import Theorems.Thm_Paper_card_rectangles
import Theorems.Thm_Paper_card_rectangles_le
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork
open Paper (Rectangle rectangles mem_rectangles card_rectangles card_rectangles_le Settings RowSetting FactorsThrough)
variable {g lam : ℕ}
namespace Eight
theorem _root_.solution (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) {a a' : Fin g} (h : a < a')
    (z z' : RowSetting g lam) :
    (rowNetwork W ι).Ψ a a' z z' = (∏ j, if z j (a', j) = z' j (a, j) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        Eight.A lam (ι ((a, a'), k)) (z k.1 (a', k.2)) (z k.2 (a', k.1)) (z' k.1 (a, k.2)) (z' k.2 (a, k.1)) :=
  Grid.rowNet_Ψ (fun q => rowCut_factors hlam (hι q)) W _ lam h z z'
end Eight
