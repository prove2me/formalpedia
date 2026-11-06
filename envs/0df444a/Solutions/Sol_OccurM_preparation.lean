-- Prove2me | solution 1 for OccurM.preparation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:04:32.371599+00:00
-- url     : https://prove2.me/submissions/086d1cc1-1c80-4e34-a42f-7151a661e693

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_OccurM_Prep
import Theorems.Thm_OccurM_prepares_rencC
import Theorems.Thm_OccurM_prepares_renc
import Theorems.Thm_VariableBound_Rename_rencC_polyT
import Theorems.Thm_VariableBound_Rename_renc_polyT


set_option autoImplicit false
section
section
open OccurM
open Groundwork MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
namespace OccurM
theorem _root_.solution : PreparationStmt := ⟨prepares_rencC, rencC_polyT, prepares_renc, renc_polyT⟩
end OccurM
