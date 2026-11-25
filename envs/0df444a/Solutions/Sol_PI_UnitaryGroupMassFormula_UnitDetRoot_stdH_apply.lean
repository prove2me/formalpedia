-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.stdH_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:11.201868+00:00
-- url     : https://prove2.me/submissions/ad5afd51-d9fd-45a6-899f-2e91738588b6

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
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.stdH L m x y = ∑ i, x i * ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * conj (y i) := by
  simp [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply]
end PI.UnitaryGroupMassFormula.UnitDetRoot
