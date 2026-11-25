-- Prove2me | solution 1 for PI.EagonNorthcottZ.Ex_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:51.488317+00:00
-- url     : https://prove2.me/submissions/42dc36b1-d3f3-4e84-9de5-63261fb2865a

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
theorem _root_.solution {D : ℕ} (s : S D) :
    Ex D (rename Sum.inl s) = map (C : ℤ →+* MvPolynomial (Fin D) ℤ) s := by
  induction s using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end PI.EagonNorthcottZ
