-- Prove2me | solution 1 for SES.toFamily_Config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:39:06.916131+00:00
-- url     : https://prove2.me/submissions/8ccb5062-95e3-421f-86fe-3fb433eec6ee

import Definitions.Def_EventStructures_General_Basic
import Definitions.Def_EventStructures_General_Stable

set_option autoImplicit true
open SES
variable {L : Type*} (S : SES L)
local infix:50 " ⊢ " => S.enable
namespace SES
theorem _root_.solution : S.toFamily.Config = S.toGES.isConf := rfl
end SES
