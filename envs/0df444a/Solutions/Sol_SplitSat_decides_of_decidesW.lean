-- Prove2me | solution 1 for SplitSat.decides_of_decidesW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:15:58.325568+00:00
-- url     : https://prove2.me/submissions/571b6d13-8059-4a18-8432-6148121bc0f9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Walk
import Definitions.Def_CountKSat_InOut
import Definitions.Def_SplitSat_Reader
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_SatTopK_length_enc
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_SplitSat_nodup_toN


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping
namespace SplitSat
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {M : StepMachine (List Unit × Fml) Bool} {δ : ℝ} {c : ℕ} (h : DecidesW k M δ c) :
    Decides (Stepped.mapIn (decU k) M) k δ c := by
  intro n φ h3
  obtain ⟨T, b, r, hb, hT⟩ := h n (Decode.toN φ) (fun D hD => by
    obtain ⟨⟨C, hC, hl⟩, h'⟩ := Decode.mem_toN hD
    exact ⟨hl ▸ h3.1 C hC, h'⟩) (nodup_toN h3.2)
  refine ⟨T, b, ?_, hb.trans (Decode.satN_toN φ), hT⟩
  have r' : M.Runs (decU k (SatK.enc k φ)) T (c * (n + 2) ^ c) b := by
    rw [stDecU k n φ hk h3.1]
    exact r
  refine (Stepped.mapIn_runs r').mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ c))
  rw [DecodeK.length_enc]
  omega
end SplitSat
