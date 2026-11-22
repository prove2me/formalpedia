-- Prove2me | solution 1 for computation_to_reachable_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:42.815902+00:00
-- url     : https://prove2.me/submissions/2c9eccc5-c2e8-4adb-8a0e-7df2e25cdf05

import Definitions.Def_EventStructures_Family_Path
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.Logic.Function.Basic
import Definitions.Def_EventStructures_Family_Computation

set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily Path Trace
theorem _root_.solution :
    Function.Surjective (computation_to_reachable F) :=
  fun ⟨c, ⟨comp⟩⟩ => ⟨⟨c, comp⟩, rfl⟩
