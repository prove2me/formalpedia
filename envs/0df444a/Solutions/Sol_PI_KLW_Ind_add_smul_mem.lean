-- Prove2me | solution 1 for PI.KLW.Ind.add_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:09.516186+00:00
-- url     : https://prove2.me/submissions/00413f06-ac65-4394-915f-4a0ae842a384

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Theorems.Thm_PI_KLW_Ind_rp_add
import Theorems.Thm_PI_KLW_Ind_rp_mul
import Theorems.Thm_PI_KLW_Ind_hf_add_left
import Theorems.Thm_PI_KLW_Ind_hf_smul_left

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
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {a b : ι → K} (ha : a ∈ L) (hb : b ∈ L)
    {r : K} (hr : Rp K p r) : a + r • b ∈ L :=
  (hL _).2 fun w hw => by
    rw [hf_add_left, hf_smul_left]
    exact rp_add ((hL a).1 ha w hw) (rp_mul hr ((hL b).1 hb w hw))
end PI.KLW.Ind
