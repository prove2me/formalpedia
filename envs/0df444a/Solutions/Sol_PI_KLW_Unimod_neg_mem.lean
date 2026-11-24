-- Prove2me | solution 1 for PI.KLW.Unimod.neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:08.607711+00:00
-- url     : https://prove2.me/submissions/dc991ac8-bd59-4b16-9ba3-8d1358fed58f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_Rp_intCast
import Theorems.Thm_PI_KLW_Unimod_smul_mem

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
theorem _root_.solution (hL : Unimod K c p L) {v : ι → K} (hv : v ∈ L) : -v ∈ L := by
  simpa using hL.smul_mem (Rp_intCast (-1)) hv
end Unimod
end PI.KLW
