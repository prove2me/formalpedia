-- Prove2me | solution 1 for PositivityTheory.KReal.fock_inner_adjoint_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:46.280316+00:00
-- url     : https://prove2.me/submissions/6e214ba5-be0d-4a5b-a95f-b8c3f5fbb7d9

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_PositivityTheory_KReal_omE_adj_gen
import Theorems.Thm_PositivityTheory_KReal_fockAct2_unit
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
theorem _root_.solution (a b : Ix r s) (u v : Pol p q r s) :
    fockInner (fockAct2 p q r s (Eab a b) u) v = epsB a b * fockInner u (fockAct2 p q r s (Eab b a) v) := by
  rw [fockAct2_unit, fockAct2_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [omE_adj_gen]
  congr 1
  cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]
end PositivityTheory.KReal
