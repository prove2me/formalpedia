-- Prove2me | solution 1 for Wrap.decidesTM_of_wraps_counter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:51:51.645291+00:00
-- url     : https://prove2.me/submissions/1403cd06-e6ac-40b4-8687-9fa46cd9a50d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_Wrap_Sim
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_WidthThree_Rates
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_Wrap_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_numSatOcc_lt
import Theorems.Thm_VariableBound_Paper_satisfiable_iff
import Theorems.Thm_VariableBound_Paper_timeMin_three_le
import Theorems.Thm_VariableBound_Rename_anyBit_binary
import Theorems.Thm_Wrap_pad4KeepsSatAndMeetsSideConditions
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal
namespace Wrap
theorem _root_.solution {pre : List Bool → List Bool} (hpre : MapsPlainToPaddedCompact pre) {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : CountsCompactKCNFWithinMinBound M C)
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wraps M pre someBit N q) {a d : ℕ}
    (hL : ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → (MainTheoremForms.encC 3 (pad4 φ)).length ≤ a * (n + 2) ^ d ∧ (Sat3.enc φ).length ≤ a * (n + 2) ^ d)
    {T : ℕ → ℕ} (hT : Covers q (9 * C) C a d T) : Sat3.DecidesTM N T := by
  intro n φ hφ
  obtain ⟨h3, hlen, h4, hle, hsat⟩ := pad4KeepsSatAndMeetsSideConditions n φ hφ
  have hm : 2 ≤ (pad4 φ).length := by omega
  obtain ⟨ev⟩ := hW (Sat3.enc φ) _ _ (by rw [hpre n φ hφ]; exact hM 3 (n + 4) (pad4 φ) (by norm_num) h3 hm h4)
  have e : someBit (SatK.binary (MainTheoremForms.numOcc (pad4 φ)) (MainTheoremForms.numSatOcc (pad4 φ))) = [decide (MainTheoremForms.numSatOcc (pad4 φ) ≠ 0)] :=
    VariableBound.Rename.anyBit_binary (VariableBound.Paper.numSatOcc_lt (pad4 φ))
  rw [e] at ev
  refine ⟨decide (MainTheoremForms.numSatOcc (pad4 φ) ≠ 0), by rw [decide_eq_true_iff, ← VariableBound.Paper.satisfiable_iff, hsat], ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩⟩
  refine le_trans ?_ (hT n _ _ _ _ hm h4 hle (hL n φ hφ).1 (hL n φ hφ).2)
  gcongr
  exact VariableBound.Paper.timeMin_three_le C hm h4
end Wrap
