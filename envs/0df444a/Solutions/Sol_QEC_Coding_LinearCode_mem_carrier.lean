-- Prove2me | solution 1 for QEC.Coding.LinearCode.mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:21:17.362367+00:00
-- url     : https://prove2.me/submissions/e2858ef7-93fb-4647-83fc-227a5b613b30

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Semantics_QuantumCode_mem_carrier

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem solution (C : LinearCode F ι) (x : Word F ι) :
    x ∈ C.carrier ↔ x ∈ (C : Submodule F (Word F ι)) := by
  rfl
