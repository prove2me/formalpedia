-- Prove2me | solution 1 for PI.OddDualWeyl.antitone_lamStar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:51.064074+00:00
-- url     : https://prove2.me/submissions/87c18a09-7f7c-4fdd-a620-37a3191f8227

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (lamStar lam) := by
  intro i j hij
  simp only [lamStar]
  exact neg_le_neg (h (Fin.rev_le_rev.mpr hij))
end PI.OddDualWeyl
