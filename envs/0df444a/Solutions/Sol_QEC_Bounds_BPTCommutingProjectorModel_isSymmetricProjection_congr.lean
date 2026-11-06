-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:20:18.19737+00:00
-- url     : https://prove2.me/submissions/d67a9607-9fb1-4076-9069-dfbb2e534c27

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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] {P Q : Semantics.Operator H}
    (hP : P.IsSymmetricProjection) (hPQ : P = Q) : Q.IsSymmetricProjection := by
  cases hPQ
  exact hP
end QEC.Bounds.BPTCommutingProjectorModel
