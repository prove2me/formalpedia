-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.contDiffOn_cF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:40.780336+00:00
-- url     : https://prove2.me/submissions/e0029d91-3eba-4e89-8886-7132888f2452

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_isUnit_eA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution (i : Fin s × Fin s × Bool) (n : ℕ) :
    ContDiffOn ℝ n (cF s i) {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} := by
  have hinv : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x | IsUnit x} := fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt
  exact (lamF s i).contDiff.comp_contDiffOn
    (hinv.comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ))
end PI.UnitaryGroupMassFormula.UsCost.ZI
