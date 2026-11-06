-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.toOperator_adjoint_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:17:37.204512+00:00
-- url     : https://prove2.me/submissions/e53c47c2-a4be-4fa9-9a58-5a99524dffaa

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (rho : DensityOperator H) :
    LinearMap.adjoint rho.toOperator = rho.toOperator :=
  rho.positive.adjoint_eq
end QEC.Semantics.DensityOperator
