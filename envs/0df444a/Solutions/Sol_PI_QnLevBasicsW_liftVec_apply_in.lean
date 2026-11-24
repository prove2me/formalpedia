-- Prove2me | solution 1 for PI.QnLevBasicsW.liftVec_apply_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:32:11.191799+00:00
-- url     : https://prove2.me/submissions/cc77ac2d-2bf9-45fb-837b-b147047e3714

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (a : Fin (2 * r' + k + 1)) (hp : p.val = a.val + i) : liftVec k i r' v p = v a := by
  have ha := a.isLt
  have h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i := by omega
  simp only [liftVec]
  rw [dif_pos h1]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega
end PI.QnLevBasicsW
