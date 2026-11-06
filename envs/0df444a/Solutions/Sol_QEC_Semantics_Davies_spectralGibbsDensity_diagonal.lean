-- Prove2me | solution 1 for QEC.Semantics.Davies.spectralGibbsDensity_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:27:41.26456+00:00
-- url     : https://prove2.me/submissions/561d052d-9366-43fb-9903-910206421c79

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity

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
    (spectralGibbsDensity b e β).toOperator = diagonal b (gibbsProbability β e) := rfl
end QEC.Semantics.Davies
