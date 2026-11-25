-- Prove2me | solution 1 for PI.EagonNorthcottZ.Ex_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:53.701899+00:00
-- url     : https://prove2.me/submissions/53240fa3-db9e-4f27-a6ac-4fee7fb1dc6b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial
namespace PI.EagonNorthcottZ
theorem _root_.solution {D : ℕ} (g : S D) : Ex D (rename Sum.inr g) = C g := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end PI.EagonNorthcottZ
