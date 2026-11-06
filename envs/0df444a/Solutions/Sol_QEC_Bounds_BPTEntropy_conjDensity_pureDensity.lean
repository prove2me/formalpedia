-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.conjDensity_pureDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:10:41.936977+00:00
-- url     : https://prove2.me/submissions/0e55c231-813f-40d4-b0ed-da62a7aba185

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    U.conjDensity (pureDensity psi hpsi) =
      pureDensity (U psi) (by
        change ‖U.toLinearIsometryEquiv psi‖ ^ 2 = 1
        rw [U.toLinearIsometryEquiv.norm_map]
        exact hpsi) := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator, pureDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne, pureDensity_toOperator]
end QEC.Bounds.BPTEntropy
