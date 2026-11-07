-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:04.529078+00:00
-- url     : https://prove2.me/submissions/70941b54-d4a7-4755-b924-a2c6dd7d852a

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
    {U V W : UnitaryGate n}
    (hUV : GlobalPhaseEquivalent U V)
    (hVW : GlobalPhaseEquivalent V W) :
    GlobalPhaseEquivalent U W := by
  rcases hUV with ⟨scalarUV, hnormUV, hmatrixUV⟩
  rcases hVW with ⟨scalarVW, hnormVW, hmatrixVW⟩
  refine ⟨scalarVW * scalarUV, ?_, ?_⟩
  · rw [norm_mul, hnormVW, hnormUV]
    norm_num
  · rw [hmatrixVW, hmatrixUV, smul_smul]
end QEC.Distillation.GeneratedUniversality
