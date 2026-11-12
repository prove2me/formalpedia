-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:59:15.08763+00:00
-- url     : https://prove2.me/submissions/0afda143-e6ce-4e9d-a12f-4328f872e466

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_errorWordWeight_eq_hammingWeight


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord m w)
    (hweight : codeDistance r w ≤ HammingWeight error) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ codeDistance r w := by
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
        (1 - epsilon.1) ^ (Fintype.card (PhysicalSite m w) - HammingWeight error) ≤
      epsilon.1 ^ HammingWeight error * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ hclean_nonneg hclean_le_one) (pow_nonneg hepsilon_nonneg _)
    _ = epsilon.1 ^ HammingWeight error := by ring
    _ ≤ epsilon.1 ^ codeDistance r w := by
      exact pow_le_pow_of_le_one hepsilon_nonneg hepsilon_le_one hweight
end QEC.Distillation.HH18Parameterized
