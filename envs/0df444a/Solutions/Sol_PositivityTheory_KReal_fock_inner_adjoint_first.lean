-- Prove2me | solution 1 for PositivityTheory.KReal.fock_inner_adjoint_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:32.575996+00:00
-- url     : https://prove2.me/submissions/01e8bb2b-5125-481c-9597-3892f6926ca2

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_PositivityTheory_KReal_omE_adj_gen
import Theorems.Thm_PositivityTheory_KReal_fockAct1_unit
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_left
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_right
import Theorems.Thm_PI_FHS_fockInner_sum_left
import Theorems.Thm_PI_FHS_fockInner_sum_right


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
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (a b : Ix p q) (u v : Pol p q r s) :
    fockInner (fockAct1 p q r s (Eab a b) u) v = epsB a b * fockInner u (fockAct1 p q r s (Eab b a) v) := by
  rw [fockAct1_unit, fockAct1_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [omE_adj_gen]
  congr 1
  cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]
end PositivityTheory.KReal
