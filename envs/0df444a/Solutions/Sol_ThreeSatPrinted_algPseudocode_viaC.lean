-- Prove2me | solution 1 for ThreeSatPrinted.algPseudocode_viaC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:28:34.432813+00:00
-- url     : https://prove2.me/submissions/5afe575f-f436-41c1-901c-ba185e1e0773

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatPrinted_Defs
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_Eight_Level_SecPseudocode
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_ThreeSatOnTree_ThmEveryDelta
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic.Positivity
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Theorems.Thm_Eight_Level_firstLevel_spec
import Theorems.Thm_Eight_ViaGrouping_algPseudocode_of
import Theorems.Thm_ThreeSatOnTree_one_le_leafCU
import Theorems.Thm_ThreeSatOnTree_sufficesSparse_viaC


set_option autoImplicit false
section
section
open ThreeSatPrinted
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight ThreeSatOnTree
namespace ThreeSatPrinted
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) :
    ∃ (τ : ℕ) (δ' : ℝ) (hδ' : 0 < δ'), 24 ≤ τ ∧ δ' = min (δ / (3 * (leafCU τ 3 : ℝ))) 1 ∧ Paper.DecidesInSteps (SATCp (Level.firstLevel hδ') τ) δ := by
  obtain ⟨τ, hτ, hS⟩ := sufficesSparse_viaC hδ
  have hM := one_le_leafCU τ
  have hδ' : 0 < min (δ / (3 * (leafCU τ 3 : ℝ))) 1 := lt_min (by positivity) one_pos
  obtain ⟨hKδ, hE⟩ := Level.firstLevel_spec hδ'
  exact ⟨τ, _, hδ', hτ, rfl, ViaGrouping.algPseudocode_of hδ hM hS hKδ hE⟩
end ThreeSatPrinted
