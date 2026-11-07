-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.transportDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:18.194974+00:00
-- url     : https://prove2.me/submissions/2f44e5d8-bda5-4696-832b-c9bd4fa484b3

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality

set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise
namespace QEC.Distillation.GeneratedUniversality
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (U : UnitaryTransport H H) (rho : DensityOperator H) :
    (transportDensity U rho).toOperator = U.conjOperator rho.toOperator :=
  rfl
end QEC.Distillation.GeneratedUniversality
