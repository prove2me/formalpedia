-- Prove2me | solution 1 for QEC.Coding.why24QuditZ_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:15:31.380846+00:00
-- url     : https://prove2.me/submissions/61bf5426-f2c9-4207-8099-7db0c17d1da2

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (γ : F1024) (ψ : Why24QuditSpace) (η : F1024) :
    why24QuditZ γ ψ η =
      PauliSymplectic.binaryPhaseScalar (Algebra.trace (ZMod 2) F1024 (γ * η)) * ψ η :=
  rfl
end QEC.Coding
