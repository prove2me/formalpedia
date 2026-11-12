-- Prove2me | solution 2 for QEC.Distillation.HH18Parameterized.noisyInput_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:39:28.315239+00:00
-- url     : https://prove2.me/submissions/596ee08b-fe8f-4076-9ebc-cc76166aa507

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (m w : Nat) :
    (noisyInput epsilon m w).toOperator =
      ∑ error : PhysicalErrorWord m w,
        (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          (HH18NoisyInput.errorWordDensity error).toOperator := by
  exact
    (HH18NoisyInput.independentNoisyTRegister_toOperator
      (ι := PhysicalSite m w) epsilon)
end QEC.Distillation.HH18Parameterized
