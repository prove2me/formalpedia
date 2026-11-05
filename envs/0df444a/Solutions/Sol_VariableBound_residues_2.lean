-- Prove2me | solution 2 for VariableBound.residues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:55:58.488979+00:00
-- url     : https://prove2.me/submissions/a3bd6e4c-5d74-4bef-a86d-c2f95f8b3dcd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_StepParity
import Theorems.Thm_VariableBound_StepParity_allEven_le_one
import Theorems.Thm_VariableBound_StepParity_term_nonneg
import Theorems.Thm_VariableBound_StepParity_Fsum_eq

set_option autoImplicit false
section
section
open VariableBound
open Finset ParityChecks AppVariables StepParity
namespace VariableBound
theorem _root_.solution : AppVariables.ResiduesStmt := by
  intro X E _ _ _ V nb L n hX
  have hX' : (Fintype.card X : ℤ) ≤ 2 ^ n := by exact_mod_cast hX
  refine ⟨⟨sum_nonneg fun ξ _ => term_nonneg V nb L ξ, ?_, ?_⟩, fun h => ?_⟩
  · have h1 : ∀ ξ ∈ (univ : Finset X), ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ ≤ ((Fintype.card E).choose (nb + 1) : ℤ) := fun ξ _ =>
      (mul_le_of_le_one_right (Int.natCast_nonneg _) (allEven_le_one V L ξ)).trans
        (by exact_mod_cast Nat.choose_le_choose (nb + 1) (card_le_univ (V ξ)))
    refine (sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul, card_univ]
    exact mul_le_mul_of_nonneg_right hX' (Int.natCast_nonneg _)
  · rw [pow_add]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_pow_clog one_lt_two _) (by positivity)
  · rw [Fsum_eq h]
    exact ⟨Int.natCast_nonneg _, le_trans (by exact_mod_cast card_le_univ _) hX'⟩
end VariableBound
