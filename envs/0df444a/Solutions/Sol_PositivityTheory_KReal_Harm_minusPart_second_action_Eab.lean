-- Prove2me | solution 1 for PositivityTheory.KReal.Harm.minusPart_second_action_Eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:13.319276+00:00
-- url     : https://prove2.me/submissions/8f892cd1-edcb-4f1c-b6c8-67331f3fd192

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Theorems.Thm_PositivityTheory_KReal_Harm_isPC_Eab
import Theorems.Thm_PI_FockOneDegW_minus2_eq
import Theorems.Thm_PI_WFJM_isPC_Eab


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
theorem _root_.solution {c d : Ix r s} (h : ¬ sameBlock c d) (g : Pol p q r s) :
    minusPart (fockAct2 p q r s (Eab c d)) g = - PI.FockOneDegW.lowOp (p := p) (q := q) c d g := by
  rw [PI.FockOneDegW.minus2_eq _ (isPC_Eab h)]
  congr 1
  rw [Finset.sum_eq_single c, Finset.sum_eq_single d]
  · simp [Eab]
  · intro y _ hy
    simp [Eab, Matrix.single_apply, Ne.symm hy]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero (fun y _ => ?_)
    simp [Eab, Matrix.single_apply, Ne.symm hx]
  · simp
end PositivityTheory.KReal.Harm
