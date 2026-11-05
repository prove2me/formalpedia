-- Prove2me | solution 1 for PaddedDescent.F.Eval.layersF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:16.678491+00:00
-- url     : https://prove2.me/submissions/3a99c7a2-f60a-459b-a436-4aef672c3fd4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_PaddedDescent_F_Eval_form_replicate
import Theorems.Thm_PaddedDescent_F_Eval_Form_len_le
import Theorems.Thm_PaddedDescent_F_Eval_foldl_cap_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)
namespace PaddedDescent.F.Eval
theorem _root_.solution {k n R m : ℕ} {pad : U} (hpad : layLen k n m R ≤ pad.length) (S : List Lvl × U) (p : U × U × U × U) (ψ : Fml)
    (hψ : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hm : ψ.length ≤ m) :
    layersF k pad S p R ψ = layersE (evalF k pad S p) p.2.1.length R ψ := by
  unfold layersF layersE
  rw [cap_eq (((form_replicate k n R).len_le (Nat.zero_le m)).trans hpad)]
  exact foldl_cap_eq hpad _ _ ψ _ 0 (form_replicate k n R) hψ (by omega)
end PaddedDescent.F.Eval
