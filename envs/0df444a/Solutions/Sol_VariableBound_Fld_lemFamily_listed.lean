-- Prove2me | solution 1 for VariableBound.Fld.lemFamily_listed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:15:40.150704+00:00
-- url     : https://prove2.me/submissions/9e758685-f19f-453d-9685-2d1cd62041bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Family
import Definitions.Def_VariableBound_Field_Cert
import Definitions.Def_VariableBound_Family_Main
import Definitions.Def_VariableBound_Field_Main
import Theorems.Thm_VariableBound_Fld_famD_isFamily
import Theorems.Thm_VariableBound_Fld_Cert_stCertFamD


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
namespace VariableBound.Fld
theorem _root_.solution : StCertFamD ∧ StFamD := ⟨Cert.stCertFamD, famD_isFamily⟩
end VariableBound.Fld
