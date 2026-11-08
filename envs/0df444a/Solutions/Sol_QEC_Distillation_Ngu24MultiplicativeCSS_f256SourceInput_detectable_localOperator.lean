-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_detectable_localOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:08.61535+00:00
-- url     : https://prove2.me/submissions/1fc13f67-a232-4f11-ab49-148e412105a2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_kernel_restrict_surjective
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_complement_separates
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_detectableOn_of_coset_locality
import Theorems.Thm_QEC_Semantics_FiniteAlphabet_localOperator_basis_diagonal_eq
import Theorems.Thm_QEC_Semantics_FiniteAlphabet_localOperator_basis_inner_eq_zero


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_5d3c569749_91
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement => Fintype.card F256))
    (hS : S.selected.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i)
    (E : Operator S.selectedSystem) :
    DetectableOn (f256SourceInput i).quantumCode (FiniteAlphabet.localOperator S E) := by
  apply (f256SourceInput i).detectableOn_of_coset_locality
    (FiniteAlphabet.localOperator S E) S.selected
    (f256SourceInput_complement_separates i S.selected hS)
    (f256SourceInput_kernel_restrict_surjective i S.selected hS)
  · intro x y hxy
    exact FiniteAlphabet.localOperator_basis_inner_eq_zero S E x y hxy
  · intro x y hxy
    exact FiniteAlphabet.localOperator_basis_diagonal_eq S E x y hxy
end QEC.Distillation.Ngu24MultiplicativeCSS
