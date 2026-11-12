-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:38:53.285908+00:00
-- url     : https://prove2.me/submissions/4f9ce26f-7a4d-4005-bdc5-298b000cb62d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_mass_exact
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_sector_bounds

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
theorem _root_.solution (beta : ℝ) : 0 ≤ mass S n beta ∧ mass S n beta ≤ 1 := by
  rw [mass_exact]
  obtain ⟨hx,hz⟩ := sector_bounds S n beta
  constructor
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hz.2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hz.2)]
end QEC.Coding.BDL26LogicalDefectStorage
