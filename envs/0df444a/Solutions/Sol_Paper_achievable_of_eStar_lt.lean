-- Prove2me | solution 1 for Paper.achievable_of_eStar_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:19:23.721324+00:00
-- url     : https://prove2.me/submissions/6cea4fd4-1eef-41f6-b0fd-45972bb5964b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Networks
import Definitions.Def_Paper_SecLevel_Grid
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_Paper_SecLevel_Recursion
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Paper_achievable_half


set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog
namespace Paper
theorem _root_.solution {e : ℝ} (he : eStar < e) (K₀ : ℕ) : ∃ K, K₀ ≤ K ∧ Achievable K e := by
  obtain ⟨e₀, ⟨-, h⟩, hlt⟩ := exists_lt_of_csInf_lt
    (s := {e : ℝ | 0 ≤ e ∧ ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e})
    ⟨1 / 2, by norm_num, fun K₀ => ⟨K₀, le_rfl, achievable_half K₀⟩⟩ he
  obtain ⟨K, hK, hA⟩ := h K₀
  exact ⟨K, hK, hA.mono hlt.le⟩
end Paper
