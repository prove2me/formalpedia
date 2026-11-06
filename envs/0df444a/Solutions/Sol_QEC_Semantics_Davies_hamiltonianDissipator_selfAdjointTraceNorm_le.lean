-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonianDissipator_selfAdjointTraceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:40:45.94834+00:00
-- url     : https://prove2.me/submissions/1a8c1168-eb67-49f8-97dd-5ae55f016735

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_dissipatorNorm_le
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem solution
    (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1)
    (rate : κ → HamiltonianFrequency H hH → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    selfAdjointTraceNormOneToOne (hamiltonianDissipator H hH A rate) ≤
      2 * Fintype.card κ * hmax :=
  weightedJump_dissipatorNorm_le (hamiltonianBasis H hH) (hamiltonianEnergies H hH)
    A hA rate hmax hm hn hu
