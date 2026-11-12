-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.hamiltonian_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:27:04.651472+00:00
-- url     : https://prove2.me/submissions/6135957e-d49f-41f2-bb28-5c3902b33a63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_actual_gibbs_eq
import Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_commutes


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
theorem _root_.solution (beta : ℝ) :
    Commute (hamiltonian S (n+2)) (reference S n beta).toOperator := by
  rw [BDL26BoundedRateDavies.actual_gibbs_eq]
  exact Davies.hamiltonianGibbs_commutes _ _ beta
end QEC.Coding.BDL26LogicalDefectStorage
