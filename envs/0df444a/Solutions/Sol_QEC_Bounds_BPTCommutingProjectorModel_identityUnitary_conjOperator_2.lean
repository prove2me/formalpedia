-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.identityUnitary_conjOperator
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:00.626903+00:00
-- url     : https://prove2.me/submissions/0441f164-f03f-472e-aae7-6019bf13bd94

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem solution (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (A : Semantics.Operator H) :
    (identityUnitary H).conjOperator A = A := by
  ext x
  simp [Semantics.UnitaryTransport.conjOperator, identityUnitary]
