-- Prove2me | solution 1 for ThmCount.wrapper_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:19:42.710558+00:00
-- url     : https://prove2.me/submissions/e922f3de-dea3-4ac0-9901-7f9de4d3f831

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_FrontEnd
import Definitions.Def_ThmCount_Rates
import Definitions.Def_Wrap_Main
import Mathlib.Tactic
import Definitions.Def_ThmCount_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_ThmCount_stPadKeepsCount
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences
namespace ThmCount
theorem _root_.solution {a d : ℕ} (hl : ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ → (SatK.enc 3 φ).length ≤ a * (n + 2) ^ d)
    {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : MainTheoremForms.ThmVariablesBFor M C) {pre : List Bool → List Bool} (hpre : MapsToPadded pre)
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wrap.Wraps M pre dropFour N q) :
    SatK.CountsTM 3 N fun n => q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q := by
  intro n φ h3
  obtain ⟨p1, -, p3⟩ := stPadKeepsCount n φ h3
  have hrun : Wrap.Outputs M (pre (SatK.enc 3 φ)) (SatK.binary (n + 4) (SatK.numSat (Wrap.pad4 φ))) (MainTheoremForms.timeN C 3 (n + 4)) := by
    rw [hpre n φ h3]
    exact hM 3 (n + 4) (Wrap.pad4 φ) (by norm_num) (by omega) p1
  obtain ⟨ev⟩ := hW _ _ _ hrun
  rw [p3] at ev
  have hle : q * (MainTheoremForms.timeN C 3 (n + 4) + (SatK.enc 3 φ).length + 1) ^ q ≤ q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hl n φ h3; omega) q)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩
end ThmCount
