-- Prove2me | solution 1 for P2M_Eight_colNetwork___9ff9d9772d4b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:25.230767+00:00
-- url     : https://prove2.me/submissions/0891bc8f-e872-40b0-affc-7157a7987f2f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Eight_colCut_factors
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
theorem _root_.solution (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) {j j' : Fin g} (h : j < j')
    (z z' : RowSetting g lam) :
    (colNetwork W ι).Ψ j j' z z' = (∏ a, if z a (j', a) = z' a (j, a) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        Eight.A lam (ι (k, (j, j'))) (z k.1 (j', k.2)) (z' k.1 (j, k.2)) (z k.2 (j', k.1)) (z' k.2 (j, k.1)) :=
  Grid.rowNet_Ψ (G := fun q x u y v => Eight.A lam (ι (q.2, q.1)) x y u v) (fun _ => colCut_factors hlam (hι _)) (Grid.trInst W) _ lam h z z'
end Eight
