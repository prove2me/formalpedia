-- Prove2me | solution 1 for PI.KLW.Unimod.zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:10.272211+00:00
-- url     : https://prove2.me/submissions/57910366-09b4-425e-8b7e-e05a475b7f3f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_Rp_zero
import Theorems.Thm_PI_KLW_hf_zero_left

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
variable {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type} [Fintype ι]
  {L : Set (ι → K)}
namespace PI.KLW
namespace Unimod
theorem _root_.solution (hL : Unimod K c p L) : (0 : ι → K) ∈ L :=
  (hL 0).2 fun w _ => by simpa [hf_zero_left] using (Rp_zero : Rp K p 0)
end Unimod
end PI.KLW
