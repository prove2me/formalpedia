-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_of_projectivelyGeneratedDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:12:21.299981+00:00
-- url     : https://prove2.me/submissions/bc8a0b6e-e562-456e-9981-0e24cf8a2c6a

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_approximatesModuloPhase_of_globalPhaseEquivalent_mem_generatedUnitaryTopologicalClosure

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
    {generators : Set (UnitaryGate n)}
    (hdense : ProjectivelyGeneratedDense generators) :
    FinitePrecisionUniversal generators := by
  intro target precision hprecision
  rcases hdense target with ⟨representative, hrepresentative, hphase⟩
  exact approximatesModuloPhase_of_globalPhaseEquivalent_mem_generatedUnitaryTopologicalClosure
    hphase hrepresentative hprecision
end QEC.Distillation.GeneratedUniversality
