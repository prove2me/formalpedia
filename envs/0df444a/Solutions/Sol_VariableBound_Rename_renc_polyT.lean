-- Prove2me | solution 1 for VariableBound.Rename.renc_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:37.260135+00:00
-- url     : https://prove2.me/submissions/1fd589e8-29ff-4d28-ac2d-b84efdc5b5e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Theorems.Thm_VariableBound_Rename_renF_polyT
import Theorems.Thm_VariableBound_Rename_encN_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_Groundwork_PolyT_snd
attribute [local fun_prop] Groundwork.PolyT.snd



set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
variable {α : Type} [Enc α]
namespace VariableBound.Rename
theorem _root_.solution : PolyT renc :=
  encN_polyT Decode.stCertDecM.1 (renF_polyT Decode.stCertDecM.2.snd)
end VariableBound.Rename
