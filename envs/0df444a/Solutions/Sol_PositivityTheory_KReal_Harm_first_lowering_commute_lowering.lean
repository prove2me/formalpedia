-- Prove2me | solution 1 for PositivityTheory.KReal.Harm.first_lowering_commute_lowering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:19.16688+00:00
-- url     : https://prove2.me/submissions/89062512-04ae-4498-b695-d29c268f63ed

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Theorems.Thm_PositivityTheory_KReal_pd_pd


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
open PositivityTheory.KReal.Harm
variable {p q r s : ℕ}
namespace PositivityTheory.KReal.Harm
theorem _root_.solution (a b : Ix p q) (c d : Ix r s) :
    Commute (low1 (r := r) (s := s) a b) (PI.FockOneDegW.lowOp (p := p) (q := q) c d) := by
  unfold low1 PI.FockOneDegW.lowOp
  refine Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => ?_
  split_ifs
  · have hp : ∀ u v : Ln p q r s, Commute ((pderiv u).toLinearMap : Module.End ℂ (Pol p q r s))
        (pderiv v).toLinearMap := fun u v => pd_pd u v
    exact ((hp _ _).mul_right (hp _ _)).mul_left ((hp _ _).mul_right (hp _ _))
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _
end PositivityTheory.KReal.Harm
