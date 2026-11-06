-- Prove2me | solution 1 for StepSparsify.servesCal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:04:43.699307+00:00
-- url     : https://prove2.me/submissions/3f4f9bc0-1011-44cf-af83-78870dd6d96b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_StepSparsify_CertThCal
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSat_Poly
import Definitions.Def_StepSparsify_CalServes
import Theorems.Thm_StepSparsify_stServesCal
import Theorems.Thm_StepSparsify_CertThCal_stCertThCal
import Theorems.Thm_StepSparsify_stAlphaS


set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma
namespace StepSparsify
theorem _root_.solution : StServesCal := stServesCal (CertThCal.stCertThCal stAlphaS)
end StepSparsify
