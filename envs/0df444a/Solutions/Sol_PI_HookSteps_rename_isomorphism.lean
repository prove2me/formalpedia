-- Prove2me | solution 1 for PI.HookSteps.rename_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:13.389972+00:00
-- url     : https://prove2.me/submissions/4353a3a1-7258-4d4e-9263-3d2797841984

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HighestWeightLastZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution : RenameIso := by
  intro σ τ φ hφ f g
  classical
  unfold fockQ
  rw [support_rename_of_injective hφ, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hφ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain φ hφ, coeff_rename_mapDomain φ hφ]
  congr 2
  rw [Finsupp.mapDomain_support_of_injective hφ, Finset.prod_image (fun a _ b _ h => hφ h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply hφ]
end PI.HookSteps
