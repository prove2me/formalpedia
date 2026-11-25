-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:46:08.709453+00:00
-- url     : https://prove2.me/submissions/c23a88d7-feef-4937-8f11-3efec29d64dc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepPrimPair

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
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (a : ℕ) (ha : 0 < a) (b : ℤ) (d : ℕ) (hd : 0 < d) (p q r s : ℝ)
    (h : (p : ℂ) * a + q * cmTheta b d = r * a + s * cmTheta b d) : p = r ∧ q = s := by
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [cmTheta] at him hre
  have hqs : q = s := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by omega)
  subst hqs
  refine ⟨?_, rfl⟩
  have h3 : p * a = r * a := by linarith
  exact mul_right_cancel₀ ha'.ne' h3
end PI.UnitaryGroupMassFormula.UnimodLocStd
