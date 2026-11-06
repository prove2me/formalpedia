-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_le_log_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:31:49.564778+00:00
-- url     : https://prove2.me/submissions/1f3bc930-8271-48dc-927c-2ac1c5adde6d

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_finite_jensen_entropyTerm_sum_le_logb_card
import Theorems.Thm_QEC_Semantics_DensityOperator_finrank_pos
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_nonnegative
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_sum_eq_one
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_sum_spectralEigenvalues


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
theorem _root_.solution (rho : DensityOperator H) :
    rho.vonNeumannEntropy <= Real.logb 2 (Module.finrank Complex H : Real) := by
  rw [rho.vonNeumannEntropy_eq_sum_spectralEigenvalues]
  exact finite_jensen_entropyTerm_sum_le_logb_card (Module.finrank Complex H) rho.finrank_pos
    rho.spectralEigenvalues (fun i => rho.spectralEigenvalues_nonnegative i)
    rho.spectralEigenvalues_sum_eq_one
end QEC.Semantics.DensityOperator
