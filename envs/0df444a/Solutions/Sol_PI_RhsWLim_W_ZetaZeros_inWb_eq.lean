-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.inWb_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:20.829541+00:00
-- url     : https://prove2.me/submissions/91371573-c02d-4732-841b-60e92591d4ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_MB_mid_wI
import Theorems.Thm_PI_RhsWLim_W_MB_wI_inj
import Theorems.Thm_PI_RhsWLim_W_MB_wI_midx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.ZetaZeros
theorem _root_.solution {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) : MB.Em k r *ᵥ wbPart k r w = w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, MB.Em, wbPart, ite_mul, one_mul, zero_mul]
  by_cases hi : MB.mid k r i
  · rw [Finset.sum_eq_single (MB.midx hi)]
    · rw [if_pos (MB.wI_midx hi).symm, MB.wI_midx hi]
    · intro m _ hm
      rw [if_neg]
      intro h
      exact hm (MB.wI_inj (h.symm.trans (MB.wI_midx hi).symm))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · refine (hw i ?_).symm
      simp only [MB.mid, not_and_or, not_le] at hi
      omega
    · intro m _
      rw [if_neg]
      intro h
      exact hi (by rw [h]; exact MB.mid_wI m)
end PI.RhsWLim.W.ZetaZeros
