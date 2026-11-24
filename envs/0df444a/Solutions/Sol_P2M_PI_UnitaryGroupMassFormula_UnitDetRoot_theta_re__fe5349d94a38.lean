-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_re__fe5349d94a38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:15.940112+00:00
-- url     : https://prove2.me/submissions/988125c3-7fce-4438-927b-7689f60443d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution : (UnitDetRootDefs.cmTheta b d).re = (b : ℝ) / 2 := by simp [UnitDetRootDefs.cmTheta]
end PI.UnitaryGroupMassFormula.UnitDetRoot
