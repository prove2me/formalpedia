-- Prove2me | solution 2 for PI.SqPairW.mem_yg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:47.99895+00:00
-- url     : https://prove2.me/submissions/92f95c67-a3fd-41cc-9ae8-88538678e0e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam

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
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} {n : 𝓞 E} {x : Fin N → E} :
    x ∈ yg L' L'' n ↔ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ x = (n : E) • m := Iff.rfl
end PI.SqPairW
