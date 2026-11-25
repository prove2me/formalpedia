-- Prove2me | solution 1 for PositivityTheory.KReal.conj_first_action_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:19.007198+00:00
-- url     : https://prove2.me/submissions/2774b30b-d8e2-401c-8824-1e3b8a42427d

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
import Theorems.Thm_PositivityTheory_KReal_cjP_smul
import Theorems.Thm_PositivityTheory_KReal_cjP_omE
import Theorems.Thm_FockRL_fockAct1_eq
import Theorems.Thm_PI_FHS_fockAct1_eq
import Theorems.Thm_PI_FHS_omAct_apply
import Theorems.Thm_PI_WFJM_fockAct1_eq


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
theorem _root_.solution (a b : Ix p q) (P : Pol p q r s) :
    cjP (fockAct1 p q r s (Eab a b) P) = fockAct1 p q r s (Eab a b) (cjP P) := by
  rw [PI.FHS.fockAct1_eq, PI.FHS.omAct_apply, PI.FHS.omAct_apply]
  show MvPolynomial.map _ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  change cjP _ = _
  rw [cjP_smul, cjP_omE]
  congr 1
  simp only [Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp
end PositivityTheory.KReal
