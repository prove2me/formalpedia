-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.DensityOperator.spectralEigenvalues_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:31.371797+00:00
-- url     : https://prove2.me/submissions/09dc7395-73bb-4a7b-a043-3b538d367ec8

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_nonnegative
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_sum_eq_one


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.DensityOperator
namespace QEC.Semantics.ThermalEncoding.DensityOperator
theorem _root_.solution (rho : DensityOperator H)
    (i : Fin (Module.finrank Complex H)) :
    rho.spectralEigenvalues i ≤ 1 := by
  rw [← rho.spectralEigenvalues_sum_eq_one]
  exact Finset.single_le_sum
    (fun j _ => rho.spectralEigenvalues_nonnegative j) (Finset.mem_univ i)
end QEC.Semantics.ThermalEncoding.DensityOperator
