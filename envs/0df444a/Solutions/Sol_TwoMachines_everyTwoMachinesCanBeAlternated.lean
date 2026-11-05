-- Prove2me | solution 1 for TwoMachines.everyTwoMachinesCanBeAlternated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:14:17.595055+00:00
-- url     : https://prove2.me/submissions/1a44740c-aaab-4231-8f06-4a0e4949bb79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_TwoMachines_Main
import Theorems.Thm_TwoMachines_alt_runs
import Theorems.Thm_P2M_TwoMachines_exists_bound__28fef89684c0
import Theorems.Thm_TwoMachines_exists_length_le
import Theorems.Thm_CountKSat_exists_tmW
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Wrap_Outputs_mono
import Theorems.Thm_Wrap_coding_exists
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution : EveryTwoMachinesCanBeAlternated := by
  intro M₁ M₂ hf₁ hf₂ pre₁ pre₂ post₁ post₂ hpre₁ hpre₂ hpost₁ hpost₂
  obtain ⟨K₁⟩ := coding_exists M₁ hf₁
  obtain ⟨K₂⟩ := coding_exists M₂ hf₂
  have := alt_isPolyT K₁ K₂ hpre₁ hpre₂ hpost₁ hpost₂
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.exists_tmW (alt K₁ K₂ pre₁ pre₂ post₁ post₂)
  obtain ⟨c₁, hc₁⟩ := exists_length_le hpre₁
  obtain ⟨c₂, hc₂⟩ := exists_length_le hpre₂
  obtain ⟨q, hq⟩ := exists_bound₂ q₀ K₁.a K₂.a c₁ c₂
  exact ⟨K₁, K₂, N, q₀, q, hfin, hN, fun x y₁ y₂ t₁ t₂ h₁ h₂ he =>
    Outputs.mono (hN x _ _ _ (alt_runs K₁ K₂ pre₁ pre₂ post₁ post₂ h₁ h₂ he)) (hq (min t₁ t₂) x.length _ _ (hc₁ x) (hc₂ x))⟩
end TwoMachines
