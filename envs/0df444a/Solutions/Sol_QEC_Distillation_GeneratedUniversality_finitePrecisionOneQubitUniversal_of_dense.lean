-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.finitePrecisionOneQubitUniversal_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:44.615042+00:00
-- url     : https://prove2.me/submissions/5d18c524-82fd-4bc0-81ff-77921b5848fc

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_finitePrecisionUniversal_of_dense

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
    (hdense : GeneratedUnitaryDense generators) :
    FinitePrecisionOneQubitUniversal generators :=
  finitePrecisionUniversal_of_dense hdense
end QEC.Distillation.GeneratedUniversality
