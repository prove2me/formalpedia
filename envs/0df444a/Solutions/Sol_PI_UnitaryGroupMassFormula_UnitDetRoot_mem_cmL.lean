-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.mem_cmL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:54.741171+00:00
-- url     : https://prove2.me/submissions/3736f6b7-85fc-481d-8dee-2ac10f593da2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____a97a4aa1fba4
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____ed65171107ba

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
theorem _root_.solution {x : ℂ} :
    x ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice ↔ ∃ p q : ℤ, x = lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d) := by
  rw [PeriodPair.mem_lattice, cmL_ω₁, cmL_ω₂]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [← h]; ring⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [h]; ring⟩
end PI.UnitaryGroupMassFormula.UnitDetRoot
