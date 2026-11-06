-- Prove2me | solution 1 for QEC.Semantics.Davies.rateSquareSum_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:08:38.923259+00:00
-- url     : https://prove2.me/submissions/6ecc9668-541f-4996-bee2-14691328a457

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators ComplexOrder
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (rate : Frequency e → ℝ) (hn : ∀ w, 0 ≤ rate w) :
    (rateSquareSum b e A rate).IsPositive := by
  apply LinearMap.isPositive_sum
  intro w _
  exact (LinearMap.isPositive_adjoint_comp_self _).smul_of_nonneg (by exact_mod_cast hn w)
end QEC.Semantics.Davies
