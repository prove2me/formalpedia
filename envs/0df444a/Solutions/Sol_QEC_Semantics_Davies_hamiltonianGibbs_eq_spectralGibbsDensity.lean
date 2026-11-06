-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonianGibbs_eq_spectralGibbsDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:12:51.843114+00:00
-- url     : https://prove2.me/submissions/60ca48bc-53ae-4004-929b-afa9e56b15e2

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Semantics_Davies_spectralGibbsDensity_basis_independent


set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]
namespace QEC.Semantics.Davies
theorem _root_.solution {ι : Type} [Fintype ι] [Nonempty ι]
    (H : Operator V) (hH : H.IsSymmetric) (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (hamiltonianGibbs H hH β).toOperator = (spectralGibbsDensity b e β).toOperator := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply spectralGibbsDensity_basis_independent H
  · intro i
    exact hH.apply_eigenvectorBasis rfl i
  · exact heigen
end QEC.Semantics.Davies
