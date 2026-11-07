-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:08:47.178178+00:00
-- url     : https://prove2.me/submissions/b0531dc4-6743-4d45-9d20-bd9eee30227b

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
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    {generators generators' : Set (UnitaryGate n)}
    (h : generators ⊆ generators') :
    generatedUnitarySubgroup generators ≤ generatedUnitarySubgroup generators' :=
  Subgroup.closure_mono h
end QEC.Distillation.GeneratedUniversality
