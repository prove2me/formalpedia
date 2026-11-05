-- Prove2me | solution 1 for VariableBound.Family.card_Om_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:06:07.962173+00:00
-- url     : https://prove2.me/submissions/3eb61c95-5739-4219-838e-9a3e3fa47442

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_univ_quad

set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [DecidableEq F]
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) :
    #(Om bits ϑ a) + #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} = Fintype.card F ^ 4 := by
  rw [Om, card_filter_add_card_filter_not, card_univ_quad]
end VariableBound.Family
