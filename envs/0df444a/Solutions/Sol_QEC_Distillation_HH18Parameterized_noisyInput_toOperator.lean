-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.noisyInput_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:31:12.296044+00:00
-- url     : https://prove2.me/submissions/03bbc245-0c66-4f2f-904f-547cdf6b82cf

import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem solution (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (m w : Nat) :
    (noisyInput epsilon m w).toOperator =
      ∑ error : PhysicalErrorWord m w,
        (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          (HH18NoisyInput.errorWordDensity error).toOperator := by
  exact
    (HH18NoisyInput.independentNoisyTRegister_toOperator
      (ι := PhysicalSite m w) epsilon)