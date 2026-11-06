-- Prove2me | solution 1 for P2M_Eight_ViaGrouping_psiLt_eq___8a678fd56db2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:00:42.189201+00:00
-- url     : https://prove2.me/submissions/6e78d3fa-914c-4723-af48-d87a8f07925c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_GridPsiDefs
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_SecCrossing_Cert
import Definitions.Def_Eight_Level_Presents
import Definitions.Def_Eight_Level_Cert
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Theorems.Thm_Eight_ViaGrouping_psiLt_row
import Theorems.Thm_Eight_ViaGrouping_psiLt_col
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {g lam : ℕ} (hlam : 1 ≤ lam) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a < b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) :
    psiLt g tr lam y a b z z' = (netOfι g tr lam y Rm).Ψ a b z z' := by
  cases tr
  · exact psiLt_row hlam y Rm hab hz hz'
  · exact psiLt_col hlam y Rm hab hz hz'
end Eight.ViaGrouping
