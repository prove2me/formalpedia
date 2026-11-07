-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_of_matrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:03.445803+00:00
-- url     : https://prove2.me/submissions/9ecf0a8e-dc79-45a6-8beb-a8a0601b6717

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
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    {U V : UnitaryGate n}
    (hmatrix : (V : Matrix n n Complex) = (U : Matrix n n Complex)) :
    GlobalPhaseEquivalent U V :=
  ⟨1, norm_one, by simpa using hmatrix⟩
end QEC.Distillation.GeneratedUniversality
