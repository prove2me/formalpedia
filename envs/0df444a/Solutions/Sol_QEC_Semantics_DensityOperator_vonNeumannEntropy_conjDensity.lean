-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_conjDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:21.67808+00:00
-- url     : https://prove2.me/submissions/60cc2625-2b2a-40e6-a428-61df238013af

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_of_charpoly_eq
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (rho : DensityOperator H) :
    (U.conjDensity rho).vonNeumannEntropy = rho.vonNeumannEntropy := by
  apply vonNeumannEntropy_eq_of_charpoly_eq
  simp [UnitaryTransport.conjDensity_toOperator,
    UnitaryTransport.conjOperator_eq_linearEquiv_conj]
end QEC.Semantics.DensityOperator
