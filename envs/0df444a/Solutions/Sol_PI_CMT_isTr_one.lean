-- Prove2me | solution 1 for PI.CMT.isTr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:46:46.346106+00:00
-- url     : https://prove2.me/submissions/489b3f99-7658-44e3-9c65-1d5bd92759cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
import Theorems.Thm_PI_CMT_isTr_mul_conj_of_mem
import Theorems.Thm_PI_CMT_trIdeal_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]
namespace PI.CMT
theorem _root_.solution
    (hP : ∀ P : Ideal (𝓞 K), P.IsMaximal →
      ∃ θ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ) ∧ θ - t ∉ P) :
    IsTr (1 : 𝓞 K) := by
  have h1 : (1 : 𝓞 K) ∈ trIdeal K := by
    rw [trIdeal_eq_top hP]
    exact Submodule.mem_top
  have h := isTr_mul_conj_of_mem h1
  rwa [map_one, mul_one] at h
end PI.CMT
