-- Prove2me | solution 1 for PI.FockOneDegW.RedOps.lowOp_Xd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:53.063954+00:00
-- url     : https://prove2.me/submissions/801d97e3-5c77-4345-8009-32aa1c9db645

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KernelHarmonic
import Theorems.Thm_PI_FockOneDegW_Core_pd_comm
import Theorems.Thm_PI_FockOneDegW_RedOps_dd_X_mul
import Theorems.Thm_PI_FockOneDegW_RedOps_lowOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}
namespace PI.FockOneDegW.RedOps
theorem _root_.solution (c d : Ix r s) (l l' : Ln p q r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (X l * pderiv l' P) =
      X l * pderiv l' (lowOp (p := p) (q := q) c d P) +
      ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
        ((if ((a, d) : Ln p q r s) = l then pderiv ((a, c) : Ln p q r s) (pderiv l' P) else 0) +
         (if ((a, c) : Ln p q r s) = l then pderiv ((a, d) : Ln p q r s) (pderiv l' P) else 0))
        else 0) := by
  rw [lowOp_apply, lowOp_apply, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : linePos ((a, d) : Ln p q r s) = true
  · simp only [h, ↓reduceIte]
    have hc : pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) (pderiv l' P)) =
        pderiv l' (pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P)) := by
      rw [PI.FockOneDegW.Core.pd_comm ((a, d) : Ln p q r s) l' P,
        PI.FockOneDegW.Core.pd_comm ((a, c) : Ln p q r s) l' (pderiv ((a, d) : Ln p q r s) P)]
    rw [dd_X_mul, hc]
    abel
  · simp [h]
end PI.FockOneDegW.RedOps
