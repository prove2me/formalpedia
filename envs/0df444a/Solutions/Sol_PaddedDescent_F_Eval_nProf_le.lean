-- Prove2me | solution 1 for PaddedDescent.F.Eval.nProf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:48:29.215325+00:00
-- url     : https://prove2.me/submissions/e5ab5d24-7118-44d5-830c-390572c50635

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)
namespace PaddedDescent.F.Eval
theorem _root_.solution (g : ℕ) {M M' R R' : ℕ} (hM : M ≤ M') (hR : R ≤ R') : nProf g M R ≤ nProf g M' R' := by
  unfold nProf
  exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hR))
end PaddedDescent.F.Eval
