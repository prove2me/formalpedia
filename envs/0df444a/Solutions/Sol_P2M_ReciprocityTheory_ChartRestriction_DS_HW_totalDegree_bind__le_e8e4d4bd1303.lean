-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_totalDegree_bind__le_e8e4d4bd1303
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:51.407806+00:00
-- url     : https://prove2.me/submissions/308122a2-b2c8-4c07-9142-555437e6eda8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = d i := mul_one _
end ReciprocityTheory.ChartRestriction.DS.HW
