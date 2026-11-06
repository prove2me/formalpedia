-- Prove2me | solution 1 for QEC.Coding.LinearCode.dimension_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:13:46.785981+00:00
-- url     : https://prove2.me/submissions/478ab8ba-9b36-49e1-ac7d-bff4e2cefe40

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C : LinearCode F ι) :
    Dimension C ≤ Length F ι := by
  rw [Dimension_eq_finrank_carrier, ← finrank_word_eq_length]
  exact Submodule.finrank_le C.carrier
end QEC.Coding.LinearCode
