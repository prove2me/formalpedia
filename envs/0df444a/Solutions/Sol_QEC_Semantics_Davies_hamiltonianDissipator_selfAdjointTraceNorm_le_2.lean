-- Prove2me | solution 2 for QEC.Semantics.Davies.hamiltonianDissipator_selfAdjointTraceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:04:20.386331+00:00
-- url     : https://prove2.me/submissions/a00eff8f-347f-4ae4-ab17-4d55235d9f95

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
namespace QEC.Semantics.Davies
theorem _root_.solution
    (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1)
    (rate : κ → HamiltonianFrequency H hH → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    selfAdjointTraceNormOneToOne (hamiltonianDissipator H hH A rate) ≤
      2 * Fintype.card κ * hmax :=
  weightedJump_dissipatorNorm_le (hamiltonianBasis H hH) (hamiltonianEnergies H hH)
    A hA rate hmax hm hn hu
end QEC.Semantics.Davies
