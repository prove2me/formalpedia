-- Prove2me | solution 1 for PI.RhsWLim.W.MB.emb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:43.93772+00:00
-- url     : https://prove2.me/submissions/d4421dc0-a28b-40ab-a44d-665fd55d9a86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_emb_form
import Theorems.Thm_PI_RhsWLim_W_MB_Hpk_eq
import Theorems.Thm_PI_RhsWLim_W_MB_sand_inj

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
theorem _root_.solution (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r a ∈ UH (Hpk k r) ↔ aᴴ * Hb k * a = Hb k := by
  show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r ↔ _
  rw [emb_form]
  constructor
  · intro h
    exact sand_inj (add_right_cancel (h.trans (Hpk_eq (k := k) (r := r))))
  · intro h
    rw [h]
    exact Hpk_eq.symm
end PI.RhsWLim.W.MB
