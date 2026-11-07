-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_shortenedCode_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:11:03.063193+00:00
-- url     : https://prove2.me/submissions/42bb0834-f44d-4f4f-93f6-07ebfc4793ed

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationCode_mem_iff
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ) :
    (f256SourceInput i).shortenedCode = (f256ShortenedMultiplicationCode i).carrier := by
  ext w
  refine Iff.trans ?_ (f256ShortenedMultiplicationCode_mem_iff i w).symm
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, x.property, ?_, rfl⟩
    intro a
    exact congrFun (LinearMap.mem_ker.mp hx) a
  · rintro ⟨x, hx, hzero, hword⟩
    exact ⟨⟨x, hx⟩, LinearMap.mem_ker.mpr (funext hzero), hword⟩
end QEC.Distillation.Ngu24MultiplicativeCSS
