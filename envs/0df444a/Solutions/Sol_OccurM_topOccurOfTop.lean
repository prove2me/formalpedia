-- Prove2me | solution 1 for OccurM.topOccurOfTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:20:43.07737+00:00
-- url     : https://prove2.me/submissions/2ba097f1-52cb-44f4-af9c-fc58101775a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_OccurM_Prep
import Definitions.Def_OccurM_Arith
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_OccurM_Top
import Theorems.Thm_OccurM_one_le_length_encC
import Theorems.Thm_OccurM_one_le_length_enc
import Theorems.Thm_OccurM_after_front
import Theorems.Thm_VariableBound_Rename_rencC_encC
import Theorems.Thm_VariableBound_Rename_rencC_polyT
import Theorems.Thm_VariableBound_Rename_renc_enc
import Theorems.Thm_VariableBound_Rename_renc_polyT


set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {α : ℝ}
namespace OccurM
theorem _root_.solution : TopOccurOfTopStmt := by
  intro Idx _ S pick α h0 h1 hT
  obtain ⟨a1, a2, a3, a4, a5⟩ := after_front h0 h1 hT (fun k _ φ => encC k φ) rencC_polyT (fun k N φ hk hφ => rencC_encC φ hk hφ.1) one_le_length_encC
  obtain ⟨b1, b2, b3, b4, b5⟩ := after_front h0 h1 hT (fun k _ φ => SatM.enc k φ) renc_polyT (fun k N φ hk hφ => renc_enc φ hk hφ.1) one_le_length_enc
  exact ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩⟩
end OccurM
