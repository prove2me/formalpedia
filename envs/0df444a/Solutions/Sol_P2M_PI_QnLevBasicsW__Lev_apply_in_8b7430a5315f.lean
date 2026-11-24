-- Prove2me | solution 1 for P2M_PI_QnLevBasicsW__Lev_apply_in_8b7430a5315f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:34:21.919372+00:00
-- url     : https://prove2.me/submissions/85ec5fbb-e978-432a-ad2a-297a628bdd1f

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
theorem _root_.solution (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (a b : Fin (2 * r' + k + 1))
    (hp : p.val = a.val + i) (hq : q.val = b.val + i) : ιLev k i r' g p q = g a b := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i := by omega
  have h2 : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i := by omega
  simp only [ιLev]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
end PI.QnLevBasicsW
