-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiagRank.det_one_sub_p_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:16.564361+00:00
-- url     : https://prove2.me/submissions/3034664d-220d-4310-bfe8-de9073b31e65

import Definitions.Def_Formalism_PeriodIntegrals_DiagRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalRank_DetOneSubPNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DiagRank
open Finset
namespace PI.UnitaryGroupMassFormula.DiagRank
theorem _root_.solution {p : ℕ} [Fact p.Prime] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ_[p]) :
    (1 - (p : ℤ_[p]) • M).det ≠ 0 := by

  intro h0
  have h1 := congrArg (PadicInt.toZMod (p := p)) h0
  rw [RingHom.map_det, map_zero] at h1
  have hI : (PadicInt.toZMod (p := p)).mapMatrix (1 - (p : ℤ_[p]) • M) = 1 := by
    ext i j
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [hI, Matrix.det_one] at h1
  exact one_ne_zero h1
end PI.UnitaryGroupMassFormula.DiagRank
