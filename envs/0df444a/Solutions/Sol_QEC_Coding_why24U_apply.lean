-- Prove2me | solution 1 for QEC.Coding.why24U_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:19:30.672177+00:00
-- url     : https://prove2.me/submissions/f77f69c5-0b20-4b98-a1b7-73422e5481d6

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (β : F1024) (n : ℕ)
    (ψ : Why24QuditSpace) (η : F1024) :
    why24U β n ψ η =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * ψ η :=
  rfl
end QEC.Coding
