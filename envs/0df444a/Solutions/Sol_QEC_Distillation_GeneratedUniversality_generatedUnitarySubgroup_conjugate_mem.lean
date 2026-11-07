-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_conjugate_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:14.526008+00:00
-- url     : https://prove2.me/submissions/f919e514-95bb-4f0c-abaa-f9aa7b244b1a

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
    U * V * U⁻¹ ∈ generatedUnitarySubgroup generators :=
  (generatedUnitarySubgroup generators).mul_mem
    ((generatedUnitarySubgroup generators).mul_mem hU hV)
    ((generatedUnitarySubgroup generators).inv_mem hU)
end QEC.Distillation.GeneratedUniversality
