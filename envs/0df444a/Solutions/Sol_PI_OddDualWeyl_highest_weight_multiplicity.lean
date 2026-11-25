-- Prove2me | solution 1 for PI.OddDualWeyl.highest_weight_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:40.382668+00:00
-- url     : https://prove2.me/submissions/3f7fa8e0-6685-4a4a-958a-8a5482c3179b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_lpMinor_row

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
open Hom
namespace PI.OddDualWeyl
theorem _root_.solution : MHhw := by
  intro R _ k ν a
  unfold hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ (fun s _ => (lpMinor_row (R := R) (s.val + 1) _ _ a).pow _)⟩
end PI.OddDualWeyl
