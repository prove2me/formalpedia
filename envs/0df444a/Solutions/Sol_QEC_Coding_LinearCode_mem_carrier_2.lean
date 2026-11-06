-- Prove2me | solution 2 for QEC.Coding.LinearCode.mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:05:42.601194+00:00
-- url     : https://prove2.me/submissions/ee864309-5832-4976-864d-0ce680dce30c

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C : LinearCode F ι) (x : Word F ι) :
    x ∈ C.carrier ↔ x ∈ (C : Submodule F (Word F ι)) :=
  Iff.rfl
end QEC.Coding.LinearCode
