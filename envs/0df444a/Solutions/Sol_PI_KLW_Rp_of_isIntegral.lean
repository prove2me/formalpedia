-- Prove2me | solution 1 for PI.KLW.Rp_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:58:10.723597+00:00
-- url     : https://prove2.me/submissions/e939fff6-dcf4-4368-b60d-92ae09157738

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
theorem _root_.solution {p : ℕ} {x : K} (h : IsIntegral ℤ x) : Rp K p x :=
  ⟨1, Nat.coprime_one_left p, by rw [Nat.cast_one, one_mul, mem_range_iff]; exact h⟩
end PI.KLW
