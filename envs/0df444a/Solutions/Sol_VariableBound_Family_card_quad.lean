-- Prove2me | solution 1 for VariableBound.Family.card_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:52.201831+00:00
-- url     : https://prove2.me/submissions/77211fe6-bea4-4e1d-8660-8fa2ac0c1136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main

set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
namespace VariableBound.Family
theorem _root_.solution (R : F × F → F × F → Prop) [∀ p r, Decidable (R p r)] :
    #{u : F × F × F × F | R (u.1, u.2.1) (u.2.2.1, u.2.2.2)} = ∑ p : F × F, #{r : F × F | R p r} := by
  simp_rw [card_filter]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun u₁ _ => ?_
  rw [Fintype.sum_prod_type]
end VariableBound.Family
