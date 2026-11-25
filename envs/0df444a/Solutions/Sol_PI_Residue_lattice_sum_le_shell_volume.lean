-- Prove2me | solution 1 for PI.Residue.lattice_sum_le_shell_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:40.968265+00:00
-- url     : https://prove2.me/submissions/90472e0d-8c4f-474b-a3db-d56a12bc83f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
import Theorems.Thm_PI_Residue_fib_le
import Theorems.Thm_PI_Residue_sum_ne_zero_le
import Theorems.Thm_PI_Residue_tsum_eq_zero_add_ne
import Theorems.Thm_PI_Residue_Fv_le

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
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (hUP : UnitPreserving) (J : (Ideal (𝓞 K))⁰) (ρ : ℝ) :
    ∑' x : lat K J, Fv ρ (x : mixedSpace K) ≤
      volume (shell K) +
        ∑' x : idealSet K J,
          volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K)) := by
  rw [tsum_eq_zero_add_ne (fun x : lat K J => Fv ρ (x : mixedSpace K))]
  refine add_le_add (Fv_le ρ _) ?_
  refine (sum_ne_zero_le J (Fv ρ)).trans ?_
  rw [ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum fun x1 => ?_
  dsimp only
  exact fib_le hUP ρ (x1 : mixedSpace K)
end PI.Residue
