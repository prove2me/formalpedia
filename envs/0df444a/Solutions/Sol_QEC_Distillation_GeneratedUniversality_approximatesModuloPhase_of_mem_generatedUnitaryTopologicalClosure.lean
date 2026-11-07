-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.approximatesModuloPhase_of_mem_generatedUnitaryTopologicalClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:43:50.157644+00:00
-- url     : https://prove2.me/submissions/1aa41c16-588a-46fe-a04a-442d42c6c230

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
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
theorem _root_.solution
    {n : Type u} [Fintype n] [DecidableEq n]
    {generators : Set (UnitaryGate n)} {target : UnitaryGate n} {precision : Real}
    (htarget : target ∈ generatedUnitaryTopologicalClosure generators)
    (hprecision : 0 < precision) :
    ApproximatesModuloPhase generators target precision :=
  ⟨target, htarget, 1, norm_one, by simpa using hprecision⟩
end QEC.Distillation.GeneratedUniversality
