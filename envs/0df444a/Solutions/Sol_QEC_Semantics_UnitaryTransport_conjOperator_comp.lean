-- Prove2me | solution 1 for QEC.Semantics.UnitaryTransport.conjOperator_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:34:01.220403+00:00
-- url     : https://prove2.me/submissions/4a3e4010-6540-4fca-ac1e-3e440eb0a49b

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.UnitaryTransport
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.UnitaryTransport
theorem _root_.solution (U : UnitaryTransport H K) (A B : Operator H) :
    U.conjOperator (A.comp B) = (U.conjOperator A).comp (U.conjOperator B) := by
  ext x
  simp [conjOperator]
end QEC.Semantics.UnitaryTransport
