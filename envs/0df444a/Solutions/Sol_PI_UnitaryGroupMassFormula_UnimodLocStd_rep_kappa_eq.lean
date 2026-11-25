-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_kappa_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:55.767246+00:00
-- url     : https://prove2.me/submissions/99e1f82f-1232-4102-9f9c-ff1b6eb0167a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_area_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : repKappa a b d ha hd lam hlam = 2 / ((Real.sqrt d : ℝ) : ℂ) := by
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsC : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hnC : ((Complex.normSq lam : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hlam).ne'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [repKappa, rep_area_eq]
  push_cast
  field_simp
end PI.UnitaryGroupMassFormula.UnimodLocStd
