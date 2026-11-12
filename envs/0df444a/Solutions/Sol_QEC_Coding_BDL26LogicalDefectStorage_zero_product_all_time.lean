-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.zero_product_all_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:16:18.644213+00:00
-- url     : https://prove2.me/submissions/509afa3d-8691-4134-9593-d04b4e23824e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_encoded_nonneg
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_decoded_nonneg
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_window_eight

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
theorem _root_.solution (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hz : g S n rate * mass S n beta = 0)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht = 0 ∧ decodedError S n rate beta eta t ht = 0 := by
  have hw : 8 * t * g S n rate * mass S n beta ≤ 0 := by
    calc
      _ = 8 * t * (g S n rate * mass S n beta) := by ring
      _ = 0 := by rw [hz,mul_zero]
      _ ≤ 0 := le_refl 0
  obtain ⟨he,hd⟩ := window_eight S n rate beta hn hDB eta 0 t (le_refl 0) ht hw
  exact ⟨le_antisymm he (encoded_nonneg S n rate beta eta t ht),
    le_antisymm hd (decoded_nonneg S n rate beta eta t ht)⟩
end QEC.Coding.BDL26LogicalDefectStorage
