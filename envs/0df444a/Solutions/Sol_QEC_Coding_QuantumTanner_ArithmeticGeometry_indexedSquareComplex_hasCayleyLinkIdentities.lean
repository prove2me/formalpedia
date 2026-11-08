-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticGeometry.indexedSquareComplex_hasCayleyLinkIdentities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:42:21.540868+00:00
-- url     : https://prove2.me/submissions/9ccf682c-a88c-4118-b56c-69ec0f11e87f

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticGeometry
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedLeft_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedLeft_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedRight_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedRight_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexed_total_nonconjugacy
import Theorems.Thm_QEC_Coding_QuantumTanner_cayleySquareComplex_hasCayleyLinkIdentities


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype K]
namespace QEC.Coding.QuantumTanner.ArithmeticGeometry
theorem _root_.solution [Fintype F]
    (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    (indexedSquareComplex f epsilon y hEpsilon hTwoF hY hOne hTwo).HasCayleyLinkIdentities := by
  unfold indexedSquareComplex
  exact cayleySquareComplex_hasCayleyLinkIdentities
    (indexedLeft f epsilon y hTwoF hY hOne hTwo)
    (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (indexedLeft_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeft_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (fun g a b => indexed_total_nonconjugacy f epsilon y hEpsilon hTwoF hY hOne hTwo a b g)
end QEC.Coding.QuantumTanner.ArithmeticGeometry
