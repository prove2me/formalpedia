-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.hJ_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:31.293803+00:00
-- url     : https://prove2.me/submissions/a436ee53-c223-4c88-91ff-1903cce53c43

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
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Jm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp <;> ring
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
