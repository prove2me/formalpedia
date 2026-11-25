-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.hpk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:29.884355+00:00
-- url     : https://prove2.me/submissions/df5b12ce-5492-426f-9b4d-d926b838541f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_hpk_eq
import Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__h__cabeda697d55
import Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_hs_h__621b40982ce1
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_star_hs
import Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__eq_iff_acb49a50f83f

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
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, hpk_eq, hpk_eq]
  by_cases h : j = hσ k r i
  · subst h
    rw [if_pos (hσ_hσ k r i).symm, if_pos rfl, star_hs, hs_hσ]
  · rw [if_neg (fun h' => h ((hσ_eq_iff k r i j).1 h')), if_neg h, star_zero]
end PI.QuotSetU.UnitaryGroupMassFormula
