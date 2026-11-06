-- Prove2me | solution 1 for QEC.Semantics.Davies.one_sub_frequency_squareSum_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:23:55.044647+00:00
-- url     : https://prove2.me/submissions/c232d307-7713-4d9a-8373-141408d6e29b

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero_positive
import Theorems.Thm_QEC_Semantics_Davies_sum_frequency_adjoint_square
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_one_zero
import Theorems.Thm_QEC_Semantics_Davies_one_sub_adjoint_square_positive
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_sub


set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) (hA : operatorNorm A ≤ 1) :
    (1 - squareSum (fun ω : Frequency e => frequencyComponent b e A ω.val)).IsPositive := by
  rw [squareSum, sum_frequency_adjoint_square,
    ← frequencyComponent_one_zero b e, ← frequencyComponent_sub]
  exact frequencyComponent_zero_positive b e _ (one_sub_adjoint_square_positive A hA)
end QEC.Semantics.Davies
