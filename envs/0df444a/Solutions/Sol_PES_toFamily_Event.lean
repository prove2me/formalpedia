-- Prove2me | solution 1 for PES.toFamily_Event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:22.269225+00:00
-- url     : https://prove2.me/submissions/bcbc0414-4b24-49c7-a443-a9a055d2ffbd

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
theorem _root_.solution : P.toFamily.Event = P.Event := rfl
end PES
