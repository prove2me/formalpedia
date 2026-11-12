-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.observable_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:30:41.272562+00:00
-- url     : https://prove2.me/submissions/22e4c6a9-8060-44a3-b7b1-2b62c0156239

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Semantics_ThermalEncoding_tensorMap_positive

section
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
section Embedding
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [FiniteQuantumSystem K]
private theorem observable_symmetric_generic (P : ThermalEncoding.PauliLikePair K)
    (eta : DensityOperator Qubit.QubitSpace) : (P.encodedObservable eta).IsSymmetric := by
  unfold ThermalEncoding.PauliLikePair.encodedObservable
  apply (P.factorization.isPositive_conjOperator ?_).isSymmetric
  exact ThermalEncoding.tensorMap_positive ((2 : ℂ) • eta.toOperator)
    (1 : Operator P.AuxiliarySpace)
    (eta.positive.smul_of_nonneg
      (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)) LinearMap.isPositive_one
end Embedding
variable (S : OddScale) (n : Nat)
end QEC.Coding.BDL26LogicalDefectStorage
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_96
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_97
namespace QEC.Coding.BDL26LogicalDefectStorage
theorem _root_.solution (eta : DensityOperator Qubit.QubitSpace) :
    (observable S n eta).IsSymmetric := observable_symmetric_generic (logical S n) eta
end QEC.Coding.BDL26LogicalDefectStorage
