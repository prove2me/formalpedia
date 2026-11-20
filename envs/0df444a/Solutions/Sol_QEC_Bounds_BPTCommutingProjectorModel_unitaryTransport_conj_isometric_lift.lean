-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_isometric_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:10:09.630843+00:00
-- url     : https://prove2.me/submissions/2646c8bb-21f2-411c-8a24-4e2a43ffd381

import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
noncomputable section
open QEC
universe u
theorem _root_.solution
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H)
    (P : Semantics.Operator S) :
    T.conjOperator (J.comp (P.comp (LinearMap.adjoint J))) =
      (T.toLinearEquiv.toLinearMap.comp J).comp
        (P.comp (LinearMap.adjoint (T.toLinearEquiv.toLinearMap.comp J))) := by
  unfold Semantics.UnitaryTransport.conjOperator
  rw [LinearMap.adjoint_comp, Semantics.UnitaryTransport.adjoint_toLinearMap]
  simp only [LinearMap.comp_assoc]
