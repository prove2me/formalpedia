-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.finitePrecisionOneQubitUniversal_of_projectivelyGeneratedDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:08.13384+00:00
-- url     : https://prove2.me/submissions/6e1c361a-825e-400a-a2f5-a8578b961369

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_finitePrecisionUniversal_of_projectivelyGeneratedDense

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
    {generators : Set (UnitaryGate (Fin 2))}
    (hdense : ProjectivelyGeneratedDense generators) :
    FinitePrecisionOneQubitUniversal generators :=
  finitePrecisionUniversal_of_projectivelyGeneratedDense hdense
end QEC.Distillation.GeneratedUniversality
