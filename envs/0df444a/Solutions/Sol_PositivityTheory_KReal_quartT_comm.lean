-- Prove2me | solution 1 for PositivityTheory.KReal.quartT_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:48.114221+00:00
-- url     : https://prove2.me/submissions/7ba8b73f-60de-4fe7-a18a-6260cc03da83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PositivityTheory PositivityTheory.KReal
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Ring E] [Algebra ℂ E]
namespace PositivityTheory.KReal
theorem _root_.solution (R L : ι → E) (hR : ∀ a b, R a * R b = R b * R a)
    (hL : ∀ a b, L a * L b = L b * L a) (A B : Matrix ι ι ℂ) :
    quartT R L A B = quartT R L B A := by
  unfold quartT
  calc ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (R i * R k * (L j * L l))
      = ∑ x : ι × ι, ∑ y : ι × ι,
          (A x.1 x.2 * B y.1 y.2) • (R x.1 * R y.1 * (L x.2 * L y.2)) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ y : ι × ι, ∑ x : ι × ι,
          (B y.1 y.2 * A x.1 x.2) • (R y.1 * R x.1 * (L y.2 * L x.2)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
        rw [mul_comm (A x.1 x.2), hR x.1, hL x.2]
    _ = _ := by simp only [Fintype.sum_prod_type]
end PositivityTheory.KReal
