-- Prove2me | solution 1 for PI.KLW.NO.c_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:44.299308+00:00
-- url     : https://prove2.me/submissions/952ef2f5-939b-40d8-ab2d-4056af12a3b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_mem_O_iff

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
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) {x : K}
    (hx : x ∈ (algebraMap (𝓞 K) K).range) : c x ∈ (algebraMap (𝓞 K) K).range :=
  mem_O_iff.2 (map_isIntegral_int c (mem_O_iff.1 hx))
end PI.KLW.NO
