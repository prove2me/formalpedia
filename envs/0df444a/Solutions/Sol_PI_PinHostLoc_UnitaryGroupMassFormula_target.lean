-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:58.307665+00:00
-- url     : https://prove2.me/submissions/ba81df76-e1db-4fbc-85c1-7dfecaea004f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_resChar_eq
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_irr
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_unit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel WithZero
open PI PI.PinHostLoc PI.PinHostLoc.UnitaryGroupMassFormula
namespace PI.PinHostLoc.UnitaryGroupMassFormula
theorem _root_.solution : PI.PinHostLoc.Target := by
  unfold PI.PinHostLoc.Target
  intro F E _ _ _ _ _ sig p A g hg hne i hin hnot
  have hres : Formalism.MainNotions.S.Loc.resChar p = g i := resChar_eq p (hg i) hin
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact irr A (hg i).ne_zero hin hnot
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have h1 : ((g 1 : ℕ) : 𝓞 F) ∉ p.asIdeal := fun h1 =>
        hne ((resChar_eq p (hg 1) h1).symm.trans hres).symm
      obtain ⟨u, hu, hu'⟩ := unit A h1
      refine ⟨u, hu, ?_⟩
      rw [hu', mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (hg 0).ne_zero)]
    · have h0 : ((g 0 : ℕ) : 𝓞 F) ∉ p.asIdeal := fun h0 =>
        hne ((resChar_eq p (hg 0) h0).symm.trans hres)
      obtain ⟨u, hu, hu'⟩ := unit A h0
      refine ⟨u, hu, ?_⟩
      rw [hu', mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (hg 1).ne_zero)]
end PI.PinHostLoc.UnitaryGroupMassFormula
