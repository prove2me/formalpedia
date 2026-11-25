-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefIntCpt_hs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:55.398269+00:00
-- url     : https://prove2.me/submissions/07ce5413-db5d-442e-8596-20f3df9ba1e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrVGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefIntCpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefIntCpt_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hq : S7.q0 ε = 0) (g : S7.UJ ε) : S7.hs (S7.toM g) = n := by
  have hu := coefIntCpt_unitary hq g
  unfold S7.hs
  have hcol : ∀ j, ∑ i, ‖S7.toM g i j‖ ^ 2 = 1 := by
    intro j
    have h := congrFun (congrFun hu j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp only [Matrix.conjTranspose_apply] at h
    have h' : ((∑ i, ‖S7.toM g i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.conj_mul']
      rfl
    exact_mod_cast h'
  rw [Finset.sum_comm]
  simp [hcol]
end ReciprocityTheory.ChartRestriction.DS
