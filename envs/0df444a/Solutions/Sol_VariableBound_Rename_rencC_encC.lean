-- Prove2me | solution 1 for VariableBound.Rename.rencC_encC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:01:29.481706+00:00
-- url     : https://prove2.me/submissions/e43fb3a4-3694-45e7-8b2b-e39d33bea455

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Theorems.Thm_VariableBound_Rename_decC_encC
import Theorems.Thm_ClauseBound_Alg_Decode_kOf_ones
import Theorems.Thm_Groundwork_DecodeK_decK_enc
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_Rename_encN_toN
import Theorems.Thm_VariableBound_Rename_toN_ren
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)
namespace VariableBound.Rename
theorem _root_.solution {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) : rencC (encC k φ) = SatM.enc k (ren φ) := by
  have e : encC k φ = List.replicate k true ++ false :: (List.replicate (Nat.log2 (2 * N) + 1) true ++ false :: bodyOf k φ) := rfl
  rw [rencC, decC_encC hk hφ, e, Decode.kOf_ones, ← encN_toN, toN_ren, renF, ← length_occL, List.map_const']
end VariableBound.Rename
