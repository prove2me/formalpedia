-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.spectralEntropy_sum_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:27.170916+00:00
-- url     : https://prove2.me/submissions/a467744b-570b-469e-96fc-ea4bb8ce55b5

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
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
theorem _root_.solution {ι : Type*} [Fintype ι]
    (rho : DensityOperator H) (e : ι ≃ Fin (Module.finrank Complex H)) :
    (∑ i, entropyTerm (rho.spectralEigenvalues (e i))) = rho.vonNeumannEntropy := by
  rw [rho.vonNeumannEntropy_eq_sum_spectralEigenvalues]
  exact Fintype.sum_equiv e _ _ (by intro i; rfl)
end QEC.Semantics.DensityOperator
