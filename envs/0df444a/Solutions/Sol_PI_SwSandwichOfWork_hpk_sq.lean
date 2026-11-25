-- Prove2me | solution 1 for PI.SwSandwichOfWork.hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:14.881136+00:00
-- url     : https://prove2.me/submissions/626b4086-4ad7-4ecb-a8e6-1c804bb4f356

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Theorems.Thm_PI_SwSandwichOfWork_Log_Hpk_eq
import Theorems.Thm_PI_SwSandwichOfWork_Log_sgI_sgI
import Theorems.Thm_PI_SwSandwichOfWork_Log_sgI_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (sgI k r i)]
  · rw [Log_Hpk_eq, Log_Hpk_eq, if_pos rfl, Log_sgI_sgI, Matrix.one_apply]
    have hv := (Log_sgI_val (k := k) (r := r) i)
    by_cases h : j = i
    · subst h
      by_cases h2 : j.val = r + k
      · rw [if_pos h2, if_pos rfl, if_pos (hv.2 h2), if_pos rfl]; norm_num
      · rw [if_neg h2, if_pos rfl, if_neg (fun h' => h2 (hv.1 h')), if_pos rfl]; norm_num
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro l _ hl; rw [Log_Hpk_eq, if_neg hl, zero_mul]
  · simp
end PI.SwSandwichOfWork
