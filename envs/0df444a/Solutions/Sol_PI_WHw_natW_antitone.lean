-- Prove2me | solution 1 for PI.WHw.natW_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:17.972196+00:00
-- url     : https://prove2.me/submissions/1542f45c-ec22-41f4-9721-137fcd804a16

import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WHw
theorem _root_.solution {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (by linarith [lam.anti hij])
end PI.WHw
