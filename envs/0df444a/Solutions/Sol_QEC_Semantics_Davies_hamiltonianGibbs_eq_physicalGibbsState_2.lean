-- Prove2me | solution 2 for QEC.Semantics.Davies.hamiltonianGibbs_eq_physicalGibbsState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:04:53.436224+00:00
-- url     : https://prove2.me/submissions/cd1a2046-4336-40ce-8914-73196969c9d1

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_eq_spectralGibbsDensity
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalHamiltonianEigenbasis_apply


set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]
namespace QEC.Semantics.Davies
theorem _root_.solution (logical : PauliLikePair V)
    (H : Operator V) (hH : H.IsSymmetric) (hX : Commute H logical.x)
    (hZ : Commute H logical.z) (β : ℝ) :
    (hamiltonianGibbs H hH β).toOperator =
      (logical.physicalGibbsState H hZ hH β).toOperator := by
  letI : Nonempty (Fin (Module.finrank ℂ logical.AuxiliarySpace)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply hamiltonianGibbs_eq_spectralGibbsDensity
  exact logical.physicalHamiltonianEigenbasis_apply H hX hZ hH
end QEC.Semantics.Davies
