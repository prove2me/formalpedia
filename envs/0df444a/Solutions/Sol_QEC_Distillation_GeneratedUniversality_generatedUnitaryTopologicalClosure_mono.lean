-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.generatedUnitaryTopologicalClosure_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:10:17.730089+00:00
-- url     : https://prove2.me/submissions/1646d26d-37ea-4a0f-917f-9daa5ae0ec4f

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_mono

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
    {generators generators' : Set (UnitaryGate n)}
    (h : generators ⊆ generators') :
    generatedUnitaryTopologicalClosure generators ⊆
      generatedUnitaryTopologicalClosure generators' := by
  apply closure_mono
  exact generatedUnitarySubgroup_mono h
end QEC.Distillation.GeneratedUniversality
