-- Prove2me | solution 1 for PI.DefPosDefWork.splitting_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:58.292805+00:00
-- url     : https://prove2.me/submissions/a679133d-85a0-45b7-b327-775c7b15aa58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_SplittingOfExtension
import Theorems.Thm_PI_DefPosDefWork_conj_of_pos
import Theorems.Thm_PI_DefPosDefWork_pos_pair

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
theorem _root_.solution : Step1 := by
  intro F E _ _ _ _ _ hreal σ k J hk _ hD φ x
  obtain ⟨r, hr⟩ := hreal (φ.comp (algebraMap F E))
  apply conj_of_pos
  intro q hq
  have hs : x + (q : E) ≠ 0 := by
    intro h0
    apply hq
    rw [← map_ratCast φ q, ← map_add, h0, map_zero]
  obtain ⟨c, hc, he⟩ := pos_pair σ J hk hD φ r (fun a => hr a) (x + q) hs
  refine ⟨c, hc, ?_⟩
  rw [← he]
  simp only [map_add, map_ratCast]
end PI.DefPosDefWork
