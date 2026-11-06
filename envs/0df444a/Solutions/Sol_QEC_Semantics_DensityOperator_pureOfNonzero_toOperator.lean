-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:00:51.932087+00:00
-- url     : https://prove2.me/submissions/19aaa1d5-6a5e-43e4-b324-57d05652695e

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
theorem _root_.solution (x : H) (hx : x ≠ 0) :
    (pureOfNonzero x hx).toOperator =
      (inner Complex x x)⁻¹ •
        (((InnerProductSpace.rankOne Complex x x : H →L[Complex] H) :
          H →ₗ[Complex] H)) :=
  rfl
end QEC.Semantics.DensityOperator
