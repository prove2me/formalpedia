-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.finitePrecisionRegisterUniversal_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:17.026086+00:00
-- url     : https://prove2.me/submissions/3dc081e8-7cd3-435d-98e1-d6e41c444256

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
theorem _root_.solution (r : Nat)
    {generators : Set (UnitaryGate (Fin (2 ^ r)))}
    (hdense : GeneratedUnitaryDense generators) :
    FinitePrecisionRegisterUniversal r generators :=
  finitePrecisionUniversal_of_dense hdense
end QEC.Distillation.GeneratedUniversality
