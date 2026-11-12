-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.clock_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:43:47.111518+00:00
-- url     : https://prove2.me/submissions/7a443760-e31f-4a91-a791-84e2cb2ab679

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_g_le
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_mass_bounds

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
theorem _root_.solution (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (t : ℝ) (ht : 0 ≤ t) :
    8 * t * g S n rate * mass S n beta ≤ 48 * t * qubits S n * hmax * mass S n beta := by
  calc
    _ ≤ 8 * t * (6 * qubits S n * hmax) * mass S n beta :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (g_le S n rate hmax hm hn hu) (by positivity))
        (mass_bounds S n beta).1
    _ = _ := by ring
end QEC.Coding.BDL26LogicalDefectStorage
