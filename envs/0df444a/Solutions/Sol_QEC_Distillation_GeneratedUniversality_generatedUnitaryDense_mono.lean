-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.generatedUnitaryDense_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:12.244165+00:00
-- url     : https://prove2.me/submissions/35223692-2cfc-440d-96c6-a6ce1ca2a365

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
    {generators generators' : Set (UnitaryGate n)}
    (h : generators ⊆ generators')
    (hdense : GeneratedUnitaryDense generators) :
    GeneratedUnitaryDense generators' := by
  apply Set.eq_univ_of_forall
  intro U
  apply generatedUnitaryTopologicalClosure_mono h
  rw [hdense]
  exact Set.mem_univ U
end QEC.Distillation.GeneratedUniversality
