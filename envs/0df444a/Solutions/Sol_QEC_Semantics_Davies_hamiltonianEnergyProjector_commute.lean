-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonianEnergyProjector_commute
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:35:57.350195+00:00
-- url     : https://prove2.me/submissions/d9b645f3-64aa-4b74-8b74-82a1049ed0dd

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
import Theorems.Thm_QEC_Semantics_Davies_energyProjector_commute
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem solution (H : Operator V) (hH : H.IsSymmetric)
    (O : Operator V) (hO : Commute H O) (E : ℝ) :
    Commute (hamiltonianEnergyProjector H hH E) O := by
  apply energyProjector_commute
  simpa only [hamiltonian_diagonal] using hO
