-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_compose_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:13.380515+00:00
-- url     : https://prove2.me/submissions/54740f8a-a39d-4f94-8007-4a119cd4f40d

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
    (generators : Set (UnitaryGate n)) {U V : UnitaryGate n}
    (hU : U ∈ generatedUnitarySubgroup generators)
    (hV : V ∈ generatedUnitarySubgroup generators) :
    U * V ∈ generatedUnitarySubgroup generators :=
  (generatedUnitarySubgroup generators).mul_mem hU hV
end QEC.Distillation.GeneratedUniversality
