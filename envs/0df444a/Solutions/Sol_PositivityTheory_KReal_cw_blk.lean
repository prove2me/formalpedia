-- Prove2me | solution 1 for PositivityTheory.KReal.cw_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:21.291891+00:00
-- url     : https://prove2.me/submissions/b8fed501-19f1-435e-9f9c-b964768000dc

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Theorems.Thm_PositivityTheory_KReal_cw_cnt_lt
import Theorems.Thm_PositivityTheory_KReal_cw_cnt_gt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {n : ℕ} (f : Fin n → ℚ) :
    ∑ i, ∑ j, (if i < j then f i - f j else 0) = ∑ i : Fin n, ((n : ℚ) - 1 - 2 * (i : ℕ)) * f i := by
  have e : ∀ i j : Fin n, (if i < j then f i - f j else 0) = (if i < j then f i else 0) - (if i < j then f j else 0) := by
    intro i j
    split_ifs <;> ring
  simp_rw [e, Finset.sum_sub_distrib, cw_cnt_lt]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j else 0)]
  simp_rw [cw_cnt_gt]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)
end PositivityTheory.KReal
