-- Prove2me | solution 1 for QEC.Semantics.Davies.hamiltonian_commutes_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:44.405124+00:00
-- url     : https://prove2.me/submissions/48934bf9-8813-4fe3-b104-97c6fb734a23

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Theorems.Thm_QEC_Semantics_Davies_spectralGibbsDensity_diagonal
import Theorems.Thm_QEC_Semantics_Davies_diagonal_commute

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) :
    Commute (diagonal b e) (spectralGibbsDensity b e β).toOperator := by
  rw [spectralGibbsDensity_diagonal]
  exact diagonal_commute b e _
end QEC.Semantics.Davies
