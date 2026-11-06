-- Prove2me | solution 1 for QEC.Semantics.Davies.rateSquareSum_operatorNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:56.346195+00:00
-- url     : https://prove2.me/submissions/1c383441-5889-4b9d-8c52-dc86fc976cd9

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Theorems.Thm_QEC_Semantics_Davies_rateSquareSum_positive
import Theorems.Thm_QEC_Semantics_Davies_rateSquareSum_defect_positive
import Theorems.Thm_QEC_Semantics_Davies_operatorNorm_le_of_positive_defect

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
    (A : Operator V) (hA : operatorNorm A ≤ 1) (rate : Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ w, 0 ≤ rate w) (hu : ∀ w, rate w ≤ hmax) :
    operatorNorm (rateSquareSum b e A rate) ≤ hmax :=
  operatorNorm_le_of_positive_defect _ hmax hm (rateSquareSum_positive b e A rate hn)
    (rateSquareSum_defect_positive b e A hA rate hmax hm hu)
end QEC.Semantics.Davies
