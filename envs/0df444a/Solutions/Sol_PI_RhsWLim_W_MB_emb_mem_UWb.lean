-- Prove2me | solution 1 for PI.RhsWLim.W.MB.emb_mem_UWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:53:29.256539+00:00
-- url     : https://prove2.me/submissions/9241e300-24f0-4046-b74d-750c0af1586a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem
import Theorems.Thm_PI_RhsWLim_W_MB_emb_fix

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
theorem _root_.solution {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : aᴴ * Hb k * a = Hb k) :
    embWb k r a ∈ UWb k r := by
  refine ⟨(emb_mem a).2 ha, fun c => ⟨emb_fix a _ ?_, emb_fix a _ ?_⟩⟩
  · have := c.isLt
    simp only [mid, eI]
    omega
  · have := c.isLt
    simp only [mid, esI]
    omega
end PI.RhsWLim.W.MB
