-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolRejectedMass_le_physicalInputCount_mul_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:01:22.678295+00:00
-- url     : https://prove2.me/submissions/ce6c4642-07b7-44a6-b69e-5b2a0d506b7c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_allZeroWord_le


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolDyadicSlackClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    1 - acceptedBernoulliMass w r m epsilon ≤
      (physicalInputCount m w : ℝ) * epsilon.1 := by
  have hrate : 0 ≤ epsilon.1 := epsilon.property.1
  calc
    1 - acceptedBernoulliMass w r m epsilon ≤
        1 - (1 - epsilon.1) ^ physicalInputCount m w := by
      exact sub_le_sub_left (acceptedBernoulliMass_allZeroWord_le h epsilon) 1
    _ ≤ (physicalInputCount m w : ℝ) * epsilon.1 := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - epsilon.1) (by linarith [epsilon.property.2])
        (physicalInputCount m w)
      nlinarith
end QEC.Distillation.HH18Parameterized
