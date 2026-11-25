-- Prove2me | solution 1 for PI.StabSplit.FixW.uOf_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:59.362277+00:00
-- url     : https://prove2.me/submissions/46d28b60-26ca-4cd0-b449-2e7552833762

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_uOf_out_row
import Theorems.Thm_PI_StabSplit_FixW_uOf_in
import Theorems.Thm_PI_StabSplit_FixW_uOf_W_out
import Theorems.Thm_PI_StabSplit_FixW_fix_col
import Theorems.Thm_PI_StabSplit_FixW_fix_zero

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
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (j : Fin (2 * r + k + 1)) (hj : j.val ≤ r + k) : uOf k r g *ᵥ yv k r g j = fun i => g i j := by
  ext i
  simp only [mulVec, dotProduct]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · have key : ∀ l, uOf k r g i l * yv k r g j l =
        if l = j then (if r ≤ j.val then g i j else 0) else 0 := by
      intro l
      by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
      · rw [uOf_in g i l hi.1 hi.2 hl.1 hl.2]
        simp only [yv, if_neg (show ¬ l.val < r by omega)]
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_pos rfl, if_pos hl.1, mul_one]
        · rw [if_neg hlj, if_neg hlj, mul_zero]
      · rw [uOf_W_out g i l hi.1 hi.2 (by omega), zero_mul]
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_neg (by omega)]
        · rw [if_neg hlj]
    rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]
    by_cases hjr : r ≤ j.val
    · rw [if_pos hjr]
    · rw [if_neg hjr, fix_col hg j (by omega) i, if_neg]; intro h; subst h; omega
  · rw [Finset.sum_eq_single i]
    · rw [uOf_out_row g i i (by omega), if_pos rfl, one_mul]
      simp only [yv]
      by_cases hir : i.val < r
      · rw [if_pos hir]
      · rw [if_neg hir, if_neg (by intro h; subst h; omega)]
        by_cases hjr : j.val < r
        · rw [fix_col hg j hjr i, if_neg (by intro h; subst h; omega)]
        · rw [fix_zero hg i j (by omega) hj]
    · intro l _ hl
      rw [uOf_out_row g i l (by omega), if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
end PI.StabSplit.FixW
