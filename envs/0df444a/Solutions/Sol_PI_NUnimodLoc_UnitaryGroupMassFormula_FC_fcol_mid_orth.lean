-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.fcol_mid_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:24.028887+00:00
-- url     : https://prove2.me/submissions/2d459bb1-8610-4fd1-964b-0dd4f5368562

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC

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
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}
variable (hF : IsFrameJ ε e f wf z0)
include hF
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution {j : Fin (2 * r + k + 1)} (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin r) :
    hJ ε (e a) (fcol k r e f wf z0 j) = 0 := by
  unfold fcol
  rw [dif_neg (by omega)]
  split_ifs with h2 h3
  · exact hF.ew a _
  · exact hF.ez a
  · exfalso; omega
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
