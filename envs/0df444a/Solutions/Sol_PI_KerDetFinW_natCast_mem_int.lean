-- Prove2me | solution 1 for PI.KerDetFinW.natCast_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:16.792591+00:00
-- url     : https://prove2.me/submissions/d68f9bf3-2b09-4d75-a866-87ac04d388ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam

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
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K : Type} [Field K] [NumberField K] (N : ℕ) :
    (N : K) ∈ (algebraMap (𝓞 K) K).range :=
  ⟨N, map_natCast _ _⟩
end PI.KerDetFinW
