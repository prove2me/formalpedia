-- Prove2me | solution 1 for PI.StabSplit.FixW.unipotent_part_fixes_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:08.51961+00:00
-- url     : https://prove2.me/submissions/ab3f9810-f684-4291-b7e3-8e1d3ae035e8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_uOf_out_row
import Theorems.Thm_PI_StabSplit_FixW_uOf_in
import Theorems.Thm_PI_StabSplit_FixW_isometry_fix_flagAnisotropicVector_of_fix_frame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g *ᵥ z = z := by
  ext i
  have hgz := congrFun (isometry_fix_flagAnisotropicVector_of_fix_frame hg) i
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · rw [← hgz]
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
    · rw [uOf_in g i l hi.1 hi.2 hl.1 hl.2]
    · rw [hz l (by omega), mul_zero, mul_zero]
  · simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · rw [uOf_out_row g i i (by omega), if_pos rfl, one_mul]
    · intro l _ hl
      rw [uOf_out_row g i l (by omega), if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
end PI.StabSplit.FixW
