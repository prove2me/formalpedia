-- Prove2me | solution 1 for VariableBound.Rename.decC_encC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:53:35.941139+00:00
-- url     : https://prove2.me/submissions/33febcb7-d621-470f-91f0-647697bb4ccb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Theorems.Thm_VariableBound_Rename_takeWhile_ones
import Theorems.Thm_VariableBound_Rename_dropWhile_ones
import Theorems.Thm_VariableBound_Rename_clausesOf_bodyOf
import Theorems.Thm_ClauseBound_Alg_Decode_kOf_ones
import Theorems.Thm_ClauseBound_Alg_Decode_restOf_ones
import Theorems.Thm_Groundwork_DecodeK_decK_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)
namespace VariableBound.Rename
theorem _root_.solution {k N : ℕ} (hk : 1 ≤ k) {φ : CNF N} (hφ : ∀ C ∈ φ, C.length ≤ k) : decC (encC k φ) = toN φ := by
  have e : encC k φ = List.replicate k true ++ false :: (List.replicate (Nat.log2 (2 * N) + 1) true ++ false :: bodyOf k φ) := rfl
  rw [decC, e, Decode.kOf_ones, Decode.restOf_ones, takeWhile_ones, dropWhile_ones, List.length_replicate]
  exact clausesOf_bodyOf hk hφ
end VariableBound.Rename
