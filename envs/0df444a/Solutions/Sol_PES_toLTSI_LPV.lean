-- Prove2me | solution 1 for PES.toLTSI_LPV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:20:04.248216+00:00
-- url     : https://prove2.me/submissions/6eb12c7d-cc99-4011-b192-49e6ed500ce2

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
import Theorems.Thm_PES_toLTSI_eq
import Theorems.Thm_ConfFamily_toLTSI_LPV


set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent
namespace PES
theorem _root_.solution : LTSI.LPV (toLTSI es) :=
  toLTSI_eq es ▸ ConfFamily.toLTSI_LPV es.toFamily
end PES
