-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonianGibbs_commutes
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:40:42.492225+00:00
-- url     : https://prove2.me/submissions/bc6c4536-f762-4c47-b6fc-d64cb377e3dc

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_commutes_gibbs
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem solution (H : Operator V) (hH : H.IsSymmetric) (β : ℝ) :
    Commute H (hamiltonianGibbs H hH β).toOperator := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  simpa only [hamiltonian_diagonal, hamiltonianGibbs] using
    hamiltonian_commutes_gibbs (hamiltonianBasis H hH) (hamiltonianEnergies H hH) β
