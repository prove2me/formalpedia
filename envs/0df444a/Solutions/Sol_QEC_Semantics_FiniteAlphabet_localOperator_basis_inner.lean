-- Prove2me | solution 1 for QEC.Semantics.FiniteAlphabet.localOperator_basis_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:17:02.516798+00:00
-- url     : https://prove2.me/submissions/3ea74926-9c34-4df0-b2bc-06ccfefb48be

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Theorems.Thm_QEC_Semantics_FiniteAlphabet_registerUnitary_apply_basis
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.FiniteAlphabet
open scoped BigOperators TensorProduct
universe u
variable (A I : Type u) [Fintype A] [Fintype I] [DecidableEq I]
attribute [local instance] QEC.Semantics.FiniteAlphabet._p2m_local_instance_ac378d2a8a_23
variable {A I}
namespace QEC.Semantics.FiniteAlphabet
theorem _root_.solution (S : QuditSubsystem (fun _ : I => Fintype.card A))
    (E : Operator S.selectedSystem) (x y : I → A) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) =
    inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel (labelEquiv A I x)).1)
        (E (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel (labelEquiv A I y)).1)) *
      inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel (labelEquiv A I x)).2)
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel (labelEquiv A I y)).2) := by
  rw [← inner_conj_symm, localOperator, UnitaryTransport.inner_conjOperator]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_symm]
  change star (inner Complex (S.extendLocalToRegister E
      (registerUnitary A I (EuclideanSpace.basisFun (I → A) Complex y)))
    (registerUnitary A I (EuclideanSpace.basisFun (I → A) Complex x))) = _
  rw [registerUnitary_apply_basis, registerUnitary_apply_basis]
  rw [QuditSubsystem.extendLocalToRegister, UnitaryTransport.inner_conjOperator]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_symm]
  rw [S.registerFactorization_apply_basis, S.registerFactorization_apply_basis,
    S.extendLocal_apply_tmul, TensorProduct.inner_tmul, star_mul]
  simp only [← starRingEnd_apply, inner_conj_symm]
  ring
end QEC.Semantics.FiniteAlphabet
