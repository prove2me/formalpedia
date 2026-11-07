-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_subset_topologicalClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:15.75376+00:00
-- url     : https://prove2.me/submissions/0e1fae85-98d6-4ac7-9b71-d0e3eb8ee600

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
theorem _root_.solution {n : Type u}
    [Fintype n] [DecidableEq n] (generators : Set (UnitaryGate n)) :
    (generatedUnitarySubgroup generators : Set (UnitaryGate n)) ⊆
      generatedUnitaryTopologicalClosure generators :=
  subset_closure
end QEC.Distillation.GeneratedUniversality
