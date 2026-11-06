-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.ext_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:12.6512+00:00
-- url     : https://prove2.me/submissions/7415c53f-836e-4676-acf3-68636a5e3f2f

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {rho sigma : DensityOperator H}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
end QEC.Semantics.DensityOperator
