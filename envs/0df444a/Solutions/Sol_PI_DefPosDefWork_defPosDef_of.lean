-- Prove2me | solution 1 for PI.DefPosDefWork.defPosDef_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:13.617933+00:00
-- url     : https://prove2.me/submissions/f3aafb46-6d62-4d5a-ad1a-080cd339666b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DefPosDefWork
open Matrix ComplexOrder
namespace PI.DefPosDefWork
theorem _root_.solution (h1 : Step1) (h2 : Step2) : PI.DefPosDef := by
  intro F E _ _ _ _ _ hF σ k J hk hH hD
  have c1 := h1 F E hF σ k J hk hH hD
  exact ⟨c1, h2 F E hF σ k J hk hH hD c1⟩
end PI.DefPosDefWork
