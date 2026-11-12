-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.errorWordWeight_le_cube_of_hammingWeight_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:16:22.807187+00:00
-- url     : https://prove2.me/submissions/5c8ecc49-2edd-4b31-a8e7-599eba00637f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_errorWordWeight_eq_hammingWeight


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord)
    (hweight : 3 ≤ HammingWeight error) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ 3 := by
  rw [HH18NoisyInput.errorWordWeight_eq_hammingWeight]
  have hepsilon_nonneg : 0 ≤ epsilon.1 := epsilon.property.1
  have hepsilon_le_one : epsilon.1 ≤ 1 := by
    linarith [epsilon.property.2]
  have hclean_nonneg : 0 ≤ 1 - epsilon.1 := by
    linarith [epsilon.property.2]
  have hclean_le_one : 1 - epsilon.1 ≤ 1 := by
    linarith [epsilon.property.1]
  calc
    epsilon.1 ^ HammingWeight error *
        (1 - epsilon.1) ^ (Fintype.card PhysicalSite - HammingWeight error) ≤
      epsilon.1 ^ HammingWeight error * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ hclean_nonneg hclean_le_one) (pow_nonneg hepsilon_nonneg _)
    _ = epsilon.1 ^ HammingWeight error := by ring
    _ ≤ epsilon.1 ^ 3 := by
      exact pow_le_pow_of_le_one hepsilon_nonneg hepsilon_le_one hweight
end QEC.Distillation.HH18Protocol
