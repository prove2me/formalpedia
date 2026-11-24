-- Prove2me | solution 1 for PI.KLW.Unimod.smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:31.95663+00:00
-- url     : https://prove2.me/submissions/65fb658f-83b8-4644-977b-eae9e09288df

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_Rp_mul
import Theorems.Thm_PI_KLW_hf_smul_left

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
theorem _root_.solution (hL : Unimod K c p L) {a : K} (ha : Rp K p a) {v : ι → K} (hv : v ∈ L) :
    a • v ∈ L :=
  (hL _).2 fun w hw => by
    rw [hf_smul_left]; exact Rp_mul ha ((hL v).1 hv w hw)
end Unimod
end PI.KLW
