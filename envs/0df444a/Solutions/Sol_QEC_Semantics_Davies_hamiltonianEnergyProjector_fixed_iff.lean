-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonianEnergyProjector_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:35:56.239768+00:00
-- url     : https://prove2.me/submissions/f3be25c7-a719-447c-94d3-f5495ea87a50

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
import Theorems.Thm_QEC_Semantics_Davies_energyProjector_fixed_iff
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem solution (H : Operator V) (hH : H.IsSymmetric)
    (E : ℝ) (x : V) :
    hamiltonianEnergyProjector H hH E x = x ↔ H x = (E : ℂ) • x := by
  simpa only [hamiltonianEnergyProjector, hamiltonian_diagonal] using
    energyProjector_fixed_iff (hamiltonianBasis H hH) (hamiltonianEnergies H hH) x E
