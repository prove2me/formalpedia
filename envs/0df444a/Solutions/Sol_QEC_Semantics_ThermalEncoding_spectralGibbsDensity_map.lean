-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.spectralGibbsDensity_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:59.141191+00:00
-- url     : https://prove2.me/submissions/ea5d47a6-5c6f-4697-a361-d3253755653f

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution {ι K : Type}
    [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K)
    (b : OrthonormalBasis ι Complex H) (energy : ι → Real) (beta : Real) :
    spectralGibbsDensity (b.map U.toLinearIsometryEquiv) energy beta =
      U.conjDensity (spectralGibbsDensity b energy beta) := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator]
  change
    (∑ i, (gibbsProbability beta energy i : Complex) •
      (InnerProductSpace.rankOne Complex
        ((b.map U.toLinearIsometryEquiv) i)
        ((b.map U.toLinearIsometryEquiv) i)).toLinearMap) =
      U.conjOperator
        (∑ i, (gibbsProbability beta energy i : Complex) •
          (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap)
  change _ = U.conjOperatorLinearMap
    (∑ i, (gibbsProbability beta energy i : Complex) •
      (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, UnitaryTransport.conjOperatorLinearMap_apply,
    QuditSubsystem.conjOperator_rankOne, OrthonormalBasis.map_apply]
  congr 1
end QEC.Semantics.ThermalEncoding
