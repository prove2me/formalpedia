-- Prove2me | solution 1 for PI.KLW.Rp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:12.87695+00:00
-- url     : https://prove2.me/submissions/437acb11-b006-42cf-84ec-8f13fc78e795

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_mem_range_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K]
namespace PI.KLW
theorem _root_.solution {p : ℕ} (c : K →+* K) {x : K} (hx : Rp K p x) : Rp K p (c x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [mem_range_iff] at *
  have := hsx.map c.toIntAlgHom
  simpa using this
end PI.KLW
