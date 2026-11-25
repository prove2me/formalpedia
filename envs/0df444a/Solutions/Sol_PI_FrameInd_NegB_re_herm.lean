-- Prove2me | solution 1 for PI.FrameInd.NegB.re_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:25.553118+00:00
-- url     : https://prove2.me/submissions/e72f4eb3-e88c-4f06-809e-bba809f3fda2

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
import Theorems.Thm_PI_FrameInd_NegB_herm_Pk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.FrameInd PI.FrameInd.NegB
namespace PI.FrameInd.NegB
theorem _root_.solution (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    (herm (Hpk k r) x x).re =
      ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) := by
  rw [herm_Pk, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i.val < r + k <;>
    simp [h, dK, epsK, Complex.mul_re, Complex.normSq_apply, Complex.star_def] <;> ring
end PI.FrameInd.NegB
