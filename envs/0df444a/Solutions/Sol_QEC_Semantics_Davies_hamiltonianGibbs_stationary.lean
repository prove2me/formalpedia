-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonianGibbs_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:40:44.793875+00:00
-- url     : https://prove2.me/submissions/f51ef2f6-901e-4f55-beff-d7495bcb1b98

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_gibbs_stationary
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem solution (H : Operator V) (hH : H.IsSymmetric)
    (A : κ → Operator V) (hA : ∀ a, (A a).IsSymmetric)
    (rate : κ → HamiltonianFrequency H hH → ℝ) (β : ℝ)
    (hn : ∀ a w, 0 ≤ rate a w)
    (hDB : ∀ a w, rate a (negFrequency (hamiltonianEnergies H hH) w) =
      Real.exp (-β*w.val) * rate a w) :
    hamiltonianDissipator H hH A rate (hamiltonianGibbs H hH β).toOperator = 0 := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  exact weightedJump_gibbs_stationary (hamiltonianBasis H hH) (hamiltonianEnergies H hH)
    β A rate hn hA hDB
