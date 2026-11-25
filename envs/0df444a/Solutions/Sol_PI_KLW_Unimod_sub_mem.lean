-- Prove2me | solution 1 for PI.KLW.Unimod.sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:46.913165+00:00
-- url     : https://prove2.me/submissions/f02db5d0-7803-4b27-ae6d-f7c1e5010cf2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_Unimod_add_mem
import Theorems.Thm_PI_KLW_Unimod_neg_mem

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
theorem _root_.solution (hL : Unimod K c p L) {v v' : ι → K} (hv : v ∈ L) (hv' : v' ∈ L) :
    v - v' ∈ L := by
  simpa [sub_eq_add_neg] using hL.add_mem hv (hL.neg_mem hv')
end Unimod
end PI.KLW
