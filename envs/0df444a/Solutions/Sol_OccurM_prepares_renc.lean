-- Prove2me | solution 1 for OccurM.prepares_renc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:57:59.720303+00:00
-- url     : https://prove2.me/submissions/739ffd11-0614-47a4-bc09-70e70234d1bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_OccurM_Prep
import Theorems.Thm_VariableBound_Rename_allOccur_ren
import Theorems.Thm_VariableBound_Rename_isKCNF_ren
import Theorems.Thm_VariableBound_Rename_length_ren
import Theorems.Thm_VariableBound_Rename_numSat_ren
import Theorems.Thm_VariableBound_Rename_renc_enc


set_option autoImplicit false
section
section
open OccurM
open Groundwork MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
namespace OccurM
theorem _root_.solution : PreparesUnary renc := fun _ _ φ hk hφ =>
  ⟨ren φ, isKCNF_ren φ hφ, allOccur_ren φ, length_ren φ, numSat_ren φ, renc_enc φ hk hφ.1⟩
end OccurM
