-- Prove2me | solution 1 for P2M_GeneralPieces_Series_Qk_eq_Qk__of_360349fc9d8f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:42.956433+00:00
-- url     : https://prove2.me/submissions/5ce9651e-dd1d-4049-9ef2-d9bd55675d39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Theorems.Thm_GeneralPieces_Series_Qk_eq_sum
import Theorems.Thm_P2M_GeneralPieces_Series_Qk__eq_sum_590380ca70a4
import Theorems.Thm_GeneralPieces_Series_Expansion_qP_eq_qM


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {A : FA} {b : List ℕ}
namespace GeneralPieces.Series
theorem _root_.solution (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) (s : ℤ) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) : Qk A b s π σ = Qk' A b s π σ := by
  rw [Qk_eq_sum hA, Qk'_eq_sum hA]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨G, hG⟩ := h c.2 b (hA c hc).1 hb
  obtain ⟨X⟩ := hG π σ hπ hσ
  rw [X.qP_eq_qM]
end GeneralPieces.Series
