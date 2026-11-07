-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:08:41.935816+00:00
-- url     : https://prove2.me/submissions/fe32477d-87d1-4fd0-8de1-8b298ae5b8b5

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
    {U V U' V' : UnitaryGate n}
    (hleft : GlobalPhaseEquivalent U V)
    (hright : GlobalPhaseEquivalent U' V') :
    GlobalPhaseEquivalent (U * U') (V * V') := by
  rcases hleft with ⟨leftScalar, hleftNorm, hleftMatrix⟩
  rcases hright with ⟨rightScalar, hrightNorm, hrightMatrix⟩
  refine ⟨leftScalar * rightScalar, ?_, ?_⟩
  · rw [norm_mul, hleftNorm, hrightNorm]
    norm_num
  · change (V : Matrix n n Complex) * (V' : Matrix n n Complex) =
      (leftScalar * rightScalar) • ((U : Matrix n n Complex) * (U' : Matrix n n Complex))
    rw [hleftMatrix, hrightMatrix, smul_mul_smul]
end QEC.Distillation.GeneratedUniversality
