-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____a97a4aa1fba4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:46:13.014801+00:00
-- url     : https://prove2.me/submissions/35bebb4d-4398-43b4-adf4-3376c8404c77

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
theorem _root_.solution : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁ = lam * a := by simp [UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]
end PI.UnitaryGroupMassFormula.UnitDetRoot
