-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.approximatesModuloPhase_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:16.785073+00:00
-- url     : https://prove2.me/submissions/85ac2237-a8e5-4de5-9ad8-a54fc7a365cc

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
    {generators : Set (UnitaryGate n)} {target : UnitaryGate n}
    {precision precision' : Real}
    (happrox : ApproximatesModuloPhase generators target precision)
    (h : precision ≤ precision') :
    ApproximatesModuloPhase generators target precision' := by
  rcases happrox with ⟨candidate, hcandidate, scalar, hscalar, hbound⟩
  exact ⟨candidate, hcandidate, scalar, hscalar, lt_of_lt_of_le hbound h⟩
end QEC.Distillation.GeneratedUniversality
