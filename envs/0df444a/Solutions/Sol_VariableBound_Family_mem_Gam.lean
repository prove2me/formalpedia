-- Prove2me | solution 1 for VariableBound.Family.mem_Gam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:53.578959+00:00
-- url     : https://prove2.me/submissions/1c50fe1f-c5e5-4759-8cd3-5d173f40a3e8

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
omit [Fintype F] [DecidableEq F]
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (u : F × F × F × F) (E : Fin m) :
    E ∈ Gam bits ϑ a u ↔ H bits ϑ a (u.1, u.2.1) E ∧ ip (bits ((u.2.2.1, u.2.2.2).1 ^ E.val)) (bits (u.2.2.1, u.2.2.2).2) = 1 := by
  simp [Gam, H]
end VariableBound.Family
