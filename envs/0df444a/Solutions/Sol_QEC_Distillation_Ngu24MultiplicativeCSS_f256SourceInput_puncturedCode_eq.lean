-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_puncturedCode_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:23:16.419227+00:00
-- url     : https://prove2.me/submissions/532fa8e2-55ba-4893-b4e4-9a77436ea279

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256PuncturedMultiplicationCode_mem_iff
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ) :
    (f256SourceInput i).code.carrier.map (f256SourceInput i).puncture =
      (f256PuncturedMultiplicationCode i).carrier := by
  ext w
  refine Iff.trans ?_ (f256PuncturedMultiplicationCode_mem_iff i w).symm
  rfl
end QEC.Distillation.Ngu24MultiplicativeCSS
