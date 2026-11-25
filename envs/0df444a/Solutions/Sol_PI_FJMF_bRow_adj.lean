-- Prove2me | solution 1 for PI.FJMF.bRow_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:02.206787+00:00
-- url     : https://prove2.me/submissions/64a54999-ce4b-4ffb-934a-3b35c733b30e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Theorems.Thm_P2M_PI_FJMF_bRow_apply__85c79f716ad7
import Theorems.Thm_PI_FJMF_inner_sum_right
import Theorems.Thm_PI_FJMF_inner_sum_left
import Theorems.Thm_PI_FJMF_inner_X_left
import Theorems.Thm_PI_FJMF_inner_pd_left

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
open PI PI.FJMF
namespace PI.FJMF
theorem _root_.solution {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (x y : MvPolynomial σ ℂ) :
    fockInner (PI.FJM.bRow ι b a x) y = fockInner x (PI.FJM.bRow ι a b y) := by
  rw [bRow_apply' ι b a x, bRow_apply' ι a b y, inner_sum_left, inner_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_X_left, inner_pd_left]
end PI.FJMF
