-- Prove2me | solution 1 for PI.KLW.NO.intCast_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:17.482825+00:00
-- url     : https://prove2.me/submissions/eaf7521e-83d2-4ac1-a6c4-ec5803e45c91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (n : ℤ) :
    (n : K) ∈ (algebraMap (𝓞 K) K).range := ⟨(n : 𝓞 K), by simp⟩
end PI.KLW.NO
