-- Prove2me | solution 1 for PositivityTheory.KReal.cw_cnt_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:01.677715+00:00
-- url     : https://prove2.me/submissions/943f6fa0-ec66-4076-bd77-41f7c7bcd4e2

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW

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
theorem _root_.solution {n : ℕ} (i : Fin n) (c : ℚ) :
    ∑ j : Fin n, (if i < j then c else 0) = ((n : ℚ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h := i.2
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring
end PositivityTheory.KReal
