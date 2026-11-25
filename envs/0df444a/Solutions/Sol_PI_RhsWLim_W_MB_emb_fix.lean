-- Prove2me | solution 1 for PI.RhsWLim.W.MB.emb_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:51.791906+00:00
-- url     : https://prove2.me/submissions/a3f268d9-2678-48bb-8d71-c54adeb78491

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_emb_out_col
import Theorems.Thm_PI_RhsWLim_W_MB_mulVec_bvec
import Theorems.Thm_PI_RhsWLim_W_MB_bvec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.MB
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.MB
theorem _root_.solution (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r a *ᵥ bvec j = bvec j := by
  ext l
  rw [mulVec_bvec, emb_out_col _ _ _ hj, bvec_apply]
end PI.RhsWLim.W.MB
