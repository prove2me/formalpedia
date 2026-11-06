-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonianJump_protected
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:40:43.631117+00:00
-- url     : https://prove2.me/submissions/afb4ea22-e9e5-43ee-be8b-ddfdac9a8173

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_protected
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem solution (H : Operator V) (hH : H.IsSymmetric)
    (A : κ → Operator V) (rate : κ → HamiltonianFrequency H hH → ℝ)
    (O P : Operator V) (hO : Commute H O) (hP : Commute H P)
    (hAP : ∀ a, (A a * O - O * A a) * P = 0) :
    JumpProtected (hamiltonianJump H hH A rate) O P := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply weightedJump_protected
  · simpa only [hamiltonian_diagonal] using hO
  · simpa only [hamiltonian_diagonal] using hP
  · exact hAP
