-- Prove2me | solution 1 for PES.toFamily_Config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:31.429595+00:00
-- url     : https://prove2.me/submissions/62d3387c-d1ba-47f8-9aaa-25a10fb45e5d

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
variable {L : Type*} (P : PES L)
namespace PES
theorem _root_.solution : P.toFamily.Config = isConf P := rfl
end PES
