-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.approximatesModuloPhase_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:12:27.873991+00:00
-- url     : https://prove2.me/submissions/8830a498-17fd-41ac-82bd-71776dfeb794

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitaryTopologicalClosure_mono

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
    {generators generators' : Set (UnitaryGate n)} {target : UnitaryGate n} {precision : Real}
    (h : generators ⊆ generators')
    (happrox : ApproximatesModuloPhase generators target precision) :
    ApproximatesModuloPhase generators' target precision := by
  rcases happrox with ⟨candidate, hcandidate, scalar, hscalar, hbound⟩
  exact ⟨candidate, generatedUnitaryTopologicalClosure_mono h hcandidate,
    scalar, hscalar, hbound⟩
end QEC.Distillation.GeneratedUniversality
