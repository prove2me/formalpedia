-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:45:22.661764+00:00
-- url     : https://prove2.me/submissions/82de1272-dde5-4819-ae8e-a98041481b28

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_approximatesModuloPhase_of_mem_generatedUnitaryTopologicalClosure
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise
namespace QEC.Distillation.GeneratedUniversality
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    {generators : Set (UnitaryGate n)}
    (hdense : GeneratedUnitaryDense generators) :
    FinitePrecisionUniversal generators := by
  intro target precision hprecision
  apply approximatesModuloPhase_of_mem_generatedUnitaryTopologicalClosure _ hprecision
  rw [hdense]
  simp
end QEC.Distillation.GeneratedUniversality
