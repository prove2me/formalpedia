-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.hpk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:34.753639+00:00
-- url     : https://prove2.me/submissions/f86c08d4-7328-4db0-ac5d-822a3a3e83b9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
namespace PI.QuotSetU.UnitaryGroupMassFormula
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = hσ k r i then hs k r i else 0 := by
  unfold Hpk hσ hs
  have hi := i.isLt
  have hj := j.isLt
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    have hne : i.val ≠ r + k := by omega
    by_cases h2 : j.val = 2 * r + k - i.val
    · have : j = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext h2
      rw [if_pos this, if_neg hne]
      rcases h1 with h1 | h1
      · rw [if_pos ⟨h1, by omega⟩]
      · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    · have : j ≠ ⟨2 * r + k - i.val, by omega⟩ := fun h => h2 (by rw [h])
      rw [if_neg this, if_neg (by omega), if_neg (by omega), if_neg]
      rintro ⟨_, _, h3⟩
      exact h2 (by rw [h3]; omega)
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h3 : j = i
    · subst h3
      simp [h1.1, h1.2]
    · rw [if_neg h3, if_neg]
      rintro ⟨_, _, h4⟩
      exact h3 h4.symm
end PI.QuotSetU.UnitaryGroupMassFormula
