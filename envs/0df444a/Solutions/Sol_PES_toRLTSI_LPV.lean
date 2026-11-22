-- Prove2me | solution 1 for PES.toRLTSI_LPV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:20:44.861454+00:00
-- url     : https://prove2.me/submissions/bc1f9fe1-7799-458b-bc5b-99d2c01456bc

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
import Theorems.Thm_ConfFamily_toRLTSI_LPV
import Theorems.Thm_PES_stable
import Theorems.Thm_SES_stable


set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent
namespace PES
theorem _root_.solution : RLTSI.LPV (toRLTSI es) :=
  ConfFamily.toRLTSI_LPV es.stable
end PES
