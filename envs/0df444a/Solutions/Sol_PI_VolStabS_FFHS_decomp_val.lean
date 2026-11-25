-- Prove2me | solution 1 for PI.VolStabS.FFHS.decomp_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:24.93702+00:00
-- url     : https://prove2.me/submissions/38852b3a-f51e-4e82-bf05-4edb44b868f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_add_left
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabS.FFHS
theorem _root_.solution (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  simp only [hs.add_right, hs.add_left, hs.smul_right, hs.smul_left, hw, hs.herm e w, map_zero]
  ring
end PI.VolStabS.FFHS
