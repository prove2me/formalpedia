-- Prove2me | solution 1 for PI.Residue.shellVolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:48.331623+00:00
-- url     : https://prove2.me/submissions/21589dc8-20c7-4062-9356-6de07451e63e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_MemSmulNormLeOne
import Theorems.Thm_PI_Residue_cHalf_pos
import Theorems.Thm_PI_Residue_cHalf_pow
import Theorems.Thm_PI_Residue_shell_eq
import Theorems.Thm_PI_Residue_smul_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution : ShellVolume := by
  intro K _ _
  have hc := cHalf_pos K
  have hV : volume (normLeOne K) = vfac K * ENNReal.ofReal (regulator K) := by
    rw [volume_normLeOne, vfac]
  have hfin : volume (normLeOne K) ≠ ⊤ := (isBounded_normLeOne K).measure_lt_top.ne
  have hs : volume (cHalf K • normLeOne K) = volume (normLeOne K) / 2 := by
    rw [Measure.addHaar_smul, mixedEmbedding.finrank, cHalf_pow, abs_of_pos (by norm_num),
      ENNReal.div_eq_inv_mul]
    congr 1
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hm : MeasurableSet (cHalf K • normLeOne K) :=
    (measurableSet_normLeOne K).const_smul₀ _
  rw [shell_eq, measure_sdiff (smul_subset K) hm.nullMeasurableSet
    (ne_top_of_le_ne_top hfin (measure_mono (smul_subset K))), hs, ← hV]
  exact ENNReal.sub_half hfin
end PI.Residue
