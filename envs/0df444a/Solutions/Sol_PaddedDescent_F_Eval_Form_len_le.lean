-- Prove2me | solution 1 for PaddedDescent.F.Eval.Form.len_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:45.451027+00:00
-- url     : https://prove2.me/submissions/988b1ff3-17e6-49a8-b6b6-55b814b57750

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_PaddedDescent_F_Eval_len_layers_le

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)
namespace PaddedDescent.F.Eval
namespace Form
theorem _root_.solution {k n R c m : ℕ} {Ls : List Fml} (h : Form k n R c Ls) (hc : c ≤ m) : len Ls ≤ layLen k n m R := by
  have h1 := len_layers_le Ls h.wf
  rw [h.layers, h.card] at h1
  have h2 : c * (k * (3 * n + 5) + 10) ≤ m * (k * (3 * n + 5) + 10) := Nat.mul_le_mul_right _ hc
  unfold layLen
  omega
end Form
end PaddedDescent.F.Eval
