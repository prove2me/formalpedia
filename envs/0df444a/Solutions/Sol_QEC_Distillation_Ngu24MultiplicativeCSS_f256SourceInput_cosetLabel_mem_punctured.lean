-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_cosetLabel_mem_punctured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:35:19.171836+00:00
-- url     : https://prove2.me/submissions/639c3afe-8e4f-428e-9b43-db343949fedb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_systematicLogicalWord_mem_code
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_puncturedCode_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ)
    (u : Fin (f256MultiplicationLogicalCount i) → F256) (h : (f256SourceInput i).H0) :
    (f256SourceInput i).shortenedCosetLabel u h ∈
      (f256PuncturedMultiplicationCode i).carrier := by
  rw [← f256SourceInput_puncturedCode_eq]
  exact ⟨(f256SourceInput i).systematicLogicalWord u + h.val.val,
    (f256SourceInput i).code.carrier.add_mem
      ((f256SourceInput i).systematicLogicalWord_mem_code u) h.val.property, rfl⟩
end QEC.Distillation.Ngu24MultiplicativeCSS
