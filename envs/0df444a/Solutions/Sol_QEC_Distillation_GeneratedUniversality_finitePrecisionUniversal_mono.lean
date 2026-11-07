-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:23.963024+00:00
-- url     : https://prove2.me/submissions/397fce70-0057-47fa-8a33-123c02bad10c

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_approximatesModuloPhase_mono

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
    (huniversal : FinitePrecisionUniversal generators) :
    FinitePrecisionUniversal generators' := by
  intro target precision hprecision
  exact approximatesModuloPhase_mono h (huniversal target precision hprecision)
end QEC.Distillation.GeneratedUniversality
