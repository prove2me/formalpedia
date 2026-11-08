-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_kernel_restrict_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:35:10.684568+00:00
-- url     : https://prove2.me/submissions/8af6bd67-5cc8-415e-ad1d-e6f734982221

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationCode_restrict_surjective
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_shortenedCode_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ)
    (S : Finset (f256SourceInput i).PivotComplement)
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    Function.Surjective (fun h : (f256SourceInput i).H0 =>
      fun j : S => (f256SourceInput i).puncture h.val.val j.val) := by
  intro values
  obtain ⟨x, hx⟩ := f256ShortenedMultiplicationCode_restrict_surjective i S hS values
  have hmem : x.val ∈ (f256SourceInput i).shortenedCode := by
    rw [f256SourceInput_shortenedCode_eq]
    exact x.property
  obtain ⟨h, hh, hword⟩ := hmem
  refine ⟨⟨h, hh⟩, ?_⟩
  change (fun j : S => (f256SourceInput i).puncture h.val j.val) = values
  rw [show (f256SourceInput i).puncture h.val = x.val from hword]
  exact hx
end QEC.Distillation.Ngu24MultiplicativeCSS
