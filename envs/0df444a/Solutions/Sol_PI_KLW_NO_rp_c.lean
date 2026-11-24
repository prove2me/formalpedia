-- Prove2me | solution 1 for PI.KLW.NO.rp_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:30.325933+00:00
-- url     : https://prove2.me/submissions/4ea47032-2cc3-4b6f-9a8f-b4a445eced0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_c_mem_O

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
open PI PI.KLW PI.KLW.NO
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW.NO
theorem _root_.solution (c : K →+* K) {x : K} (hx : Rp K p x) : Rp K p (c x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨s, hs, ?_⟩
  have : (s : K) * c x = c ((s : K) * x) := by rw [map_mul, map_natCast]
  rw [this]; exact c_mem_O c hsx
end PI.KLW.NO
