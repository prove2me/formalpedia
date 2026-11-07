-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:08.625536+00:00
-- url     : https://prove2.me/submissions/931dc6bc-5dc9-4e7f-a2b6-d53111b3f107

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_mul
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_inv

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
    {U V U' V' : UnitaryGate n}
    (hconjugator : GlobalPhaseEquivalent U V)
    (hconjugated : GlobalPhaseEquivalent U' V') :
    GlobalPhaseEquivalent (U * U' * U⁻¹) (V * V' * V⁻¹) :=
  globalPhaseEquivalent_mul
    (globalPhaseEquivalent_mul hconjugator hconjugated)
    (globalPhaseEquivalent_inv hconjugator)
end QEC.Distillation.GeneratedUniversality
