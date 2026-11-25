-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:01.732145+00:00
-- url     : https://prove2.me/submissions/6a412dea-555a-467e-a5cd-949154cc9e90

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
theorem _root_.solution {m : Type} {L : PeriodPair} {x : m → ℂ} : x ∈ UnitDetRootDefs.stdLat L m ↔ ∀ i, x i ∈ L.lattice := by
  simp [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]
end PI.UnitaryGroupMassFormula.UnitDetRoot
