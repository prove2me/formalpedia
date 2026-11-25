-- Prove2me | solution 1 for PI.SqPairLocal.cj_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:40.631106+00:00
-- url     : https://prove2.me/submissions/5270a1b8-231c-470d-95d0-59de0799c7c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution {I : Ideal (𝓞 E)} {K : ℕ} {x : 𝓞 E} (h : x ∈ (I.comap (cj E)) ^ K) :
    cj E x ∈ I ^ K := by
  have h' := Ideal.le_comap_pow (cj E) K h
  first
    | exact Ideal.mem_comap.mp h'
    | exact h'
end PI.SqPairLocal
