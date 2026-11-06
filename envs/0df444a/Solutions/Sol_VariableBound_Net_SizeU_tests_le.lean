-- Prove2me | solution 1 for VariableBound.Net.SizeU.tests_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:50.364853+00:00
-- url     : https://prove2.me/submissions/060c739e-65bc-40d8-b9d0-884485b0c474

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
import Theorems.Thm_VariableBound_Net_SizeU_nb_mul_sum_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_VariableBound_Net_Tests_card_kind_one
import Theorems.Thm_VariableBound_Net_Tests_card_kind_zero
import Theorems.Thm_VariableBound_Net_Tests_sum_length_tst_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (g : ℕ) (hk : 1 ≤ k) (hW : WfD k n D) (hrow : ∀ L ∈ D.2, nb * L.length ≤ 16 * D.1.length) :
    ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b 0).length ≤ (k - 1) * D.1.length ∧
      ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b 1).length ≤ k * (D.2.map List.length).sum ∧
      nb * (D.2.map List.length).sum ≤ D.2.length * (16 * D.1.length) := by
  refine ⟨?_, ?_, nb_mul_sum_le nb _ D.2 hrow⟩
  · have h := Tests.sum_length_tst_le (g := g) hW 0
    rwa [Tests.card_kind_zero hW, Nat.add_zero] at h
  · have h := Tests.sum_length_tst_le (g := g) hW 1
    rwa [Tests.card_kind_one hW, Nat.sub_add_cancel hk] at h
end VariableBound.Net.SizeU
