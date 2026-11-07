-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.approximatesModuloPhase_of_globalPhaseEquivalent_mem_generatedUnitaryTopologicalClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:10:49.786932+00:00
-- url     : https://prove2.me/submissions/d3f4afba-864f-4d96-8ec2-22957a18105a

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_symm
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_approximatesModuloPhase_congr_target
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_approximatesModuloPhase_of_mem_generatedUnitaryTopologicalClosure

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
    {generators : Set (UnitaryGate n)} {target representative : UnitaryGate n} {precision : Real}
    (hphase : GlobalPhaseEquivalent target representative)
    (hrepresentative : representative ∈ generatedUnitaryTopologicalClosure generators)
    (hprecision : 0 < precision) :
    ApproximatesModuloPhase generators target precision :=
  approximatesModuloPhase_congr_target (globalPhaseEquivalent_symm hphase)
    (approximatesModuloPhase_of_mem_generatedUnitaryTopologicalClosure hrepresentative hprecision)
end QEC.Distillation.GeneratedUniversality
