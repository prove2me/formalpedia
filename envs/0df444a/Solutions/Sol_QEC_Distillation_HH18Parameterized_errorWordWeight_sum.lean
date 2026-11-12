-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.errorWordWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:08:33.500118+00:00
-- url     : https://prove2.me/submissions/2ccb2398-fd00-47d0-8a3e-6a8a4fda9eff

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

theorem solution (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ∑ error : PhysicalErrorWord m w,
      HH18NoisyInput.errorWordWeight epsilon error = 1 := by
  simpa only [PhysicalErrorWord] using
    (HH18NoisyInput.errorWordWeight_sum (ι := PhysicalSite m w) epsilon)