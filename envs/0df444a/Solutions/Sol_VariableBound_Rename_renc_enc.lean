-- Prove2me | solution 1 for VariableBound.Rename.renc_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:39:37.790328+00:00
-- url     : https://prove2.me/submissions/44617aba-8597-404a-a7b3-e96118f2f204

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Paper_Rename_Code
import Theorems.Thm_VariableBound_Rename_encN_toN
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_Rename_toN_ren
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
namespace VariableBound.Rename
theorem _root_.solution {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) : renc (SatM.enc k φ) = SatM.enc k (ren φ) := by
  obtain ⟨h1, h2⟩ := Decode.stDecM k N φ hk hφ
  rw [renc, h1, h2, ← encN_toN, toN_ren, renF, ← length_occL, List.map_const']
end VariableBound.Rename
